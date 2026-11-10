-- Prove2me | Theorems.Thm_MMSSevenNinths_Main_lemma_2_4
-- name    : MMSSevenNinths.Main.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:48:46.348458+00:00
-- url     : https://prove2.me/theorems/25d79b4b-70ed-4a8b-b92d-09d9c5dea9f8
-- title:
--   Lemma 2.4 — ordered instance with the same MMS values and value-preserving allocation conversion, in polynomial time
-- statement:
--   Let $n\ge1$ agents have nonnegative additive valuations $v_i$ over the goods $M=\{e_1,\dots,e_m\}$. Let $\hat I$ be the instance on the ranks $\hat e_1,\dots,\hat e_m$ in which $\hat v_i(\hat e_r)$ is agent $i$'s $r$-th largest singleton value, extended additively (`orderedInstance`), and for an allocation $\hat\sigma$ of $\hat I$ let $\sigma=$ `convertBack V σ̂` be the allocation of $I$ obtained by letting the owners of $\hat e_1,\hat e_2,\dots$ in turn take their favourite remaining original good. Then:
--
--   1. $\hat I$ is an ordered instance with nonnegative additive valuations, and $\mathrm{MMS}_i(\hat I)=\mathrm{MMS}_i(I)$ for every agent $i$;
--   2. for every allocation $\hat B$ of $\hat I$, the converted allocation $B$ satisfies $v_i(B_i)\ge\hat v_i(\hat B_i)$ for every agent $i$;
--   3. there are two fixed LP-free programs of the exact register machine and constants $C,d$, chosen before $n$, $m$ and the values, such that the first computes the singleton values of $\hat I$ from those of $I$ and the second computes $B$ from $I$ and $\hat B$, each within $C(n+m+1)^d$ executed instructions; on rational inputs every register at every step has encoding length at most $C(L+1)^d$, where $L$ is the input length.
--
--   Differences from the source:
--   - generalization: we can construct in polynomial time an ordered instance Î with the same MMS values, and convert any allocation of Î in polynomial time into an allocation B with v_i(B_i) ≥ v̂_i(B̂_i) (existence of a construction and a conversion) → the stated properties for the specific [BK20 §3.1] construction orderedInstance and conversion convertBack, together with programs computing exactly them; reason: a statement about a named construction implies the existential one; it is the construction the paper uses in the proof of Theorem 8.1 (p. 26)
--   - generalization: polynomial time → a fixed LP-free register program (chosen with C, d before n, m and the values) halting within C·(n+m+1)^d executed instructions, and on rational inputs keeping every register at every step within encoding length C·(L+1)^d, L the input length; reason: the source promises polynomial time; the named sorting and greedy-selection construction additionally has a value-independent operation bound and polynomial rational register sizes, which imply the full polynomial-time claim
--   - encoding: agents N = {1,…,n} with n ≥ 1, goods e_1,…,e_m in the common order → agents Fin n (agent i+1 is i) with hypothesis 0 < n, goods Fin m (e_{g+1} is g); reason: zero-based finite indexing; n ≥ 1 is implicit in the MMS (an n-partition) and in v_i(M)/n; same instances
--   - encoding: an allocation is an n-partition (B_1,…,B_n) of M → an owner map σ : Fin m → Fin n with B_i = bundle σ i; reason: an owner map is exactly a complete, pairwise disjoint labelled partition with possibly empty bundles; same objects
--   - encoding: valuation functions v_i : 2^M → ℝ≥0 that are additive → V : Fin n → Finset (Fin m) → ℝ with the published IsAdditive V (additivity and nonnegativity); reason: same instances
--   - encoding: the instance and allocation given to the algorithm → machine input: n, m in natural registers; singleton values row-major followed by the ranks' integer owners (for conversion) in real registers; outputs in real registers (MatrixOutput, OwnerOutput); reason: real memory supports indirect loads and stores; natural-register addresses in the reused instruction set are fixed, so arbitrary-length owner arrays must use real memory; integer owners are exact real or rational casts
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, Lemma 2.4, printed p. 4 (PDF 7)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_DynStochMatching_Reward_RealMachine
import Definitions.Def_MMSSevenNinths_Main_Instance
import Definitions.Def_MMSSevenNinths_Main_OrderedReduction
import Definitions.Def_MMSSevenNinths_Main_Machine

namespace MMSSevenNinths.Main

open DynStochMatching.Reward LittleCharity.MMS

/-- Huang and Zhou (2026), held STOC 2027 submission, Lemma 2.4 ([BK20, §3.1]), printed p. 4
(PDF 7). For every instance with nonnegative additive valuations, the ordered instance
`orderedInstance V` (sorted singleton values) is a nonnegative additive ordered instance with the
same MMS value for every agent; `convertBack V σ̂` converts every allocation `σ̂` of it into an
allocation of the original instance in which every agent's value is at least her value for
`σ̂`; and both maps are computed by fixed LP-free register-machine programs in a number of steps
polynomial in `n + m`, with every intermediate value of polynomial encoding length on rational
inputs. The program and the constants `C`, `d` are chosen before `n`, `m` and the values. -/
theorem lemma_2_4 :
    ∃ codeOrd codeConv : List Instruction, LPFree codeOrd ∧ LPFree codeConv ∧
    ∃ C d : ℕ,
      (∀ (n m : ℕ), 0 < n → ∀ V : Fin n → Finset (Fin m) → ℝ, IsAdditive V →
        IsAdditive (orderedInstance V) ∧ IsOrdered (orderedInstance V) ∧
        (∀ i : Fin n, MMS (orderedInstance V) i = MMS V i) ∧
        (∀ (σh : Fin m → Fin n) (i : Fin n),
          orderedInstance V i (bundle σh i) ≤ V i (bundle (convertBack V σh) i)) ∧
        HaltsWithin codeOrd (machineInput [n, m] (instanceReals V)) (C * (n + m + 1) ^ d)
          (fun s => MatrixOutput s (fun i r => orderedInstance V i {r})) ∧
        (∀ σh : Fin m → Fin n,
          HaltsWithin codeConv
            (machineInput [n, m]
              (instanceReals V ++ List.ofFn (fun r => ((σh r).val : ℝ))))
            (C * (n + m + 1) ^ d) (fun s => OwnerOutput s (convertBack V σh)))) ∧
      (∀ (n m : ℕ), 0 < n → ∀ Q : Fin n → Fin m → ℚ, (∀ i g, 0 ≤ Q i g) →
        SizesWithin codeOrd (machineInput [n, m] ((ratEntries Q).map (fun q => (q : ℝ))))
          (C * (n + m + 1) ^ d) (C * (inputLength [n, m] (ratEntries Q) + 1) ^ d) ∧
        ∀ σh : Fin m → Fin n,
          SizesWithin codeConv
            (machineInput [n, m]
              (((ratEntries Q).map (fun q => (q : ℝ))) ++
                List.ofFn (fun r => ((σh r).val : ℝ))))
            (C * (n + m + 1) ^ d)
            (C * (inputLength [n, m]
              (ratEntries Q ++ List.ofFn (fun r => ((σh r).val : ℚ))) + 1) ^ d)) := by sorry

end MMSSevenNinths.Main
