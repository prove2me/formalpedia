-- Prove2me | Theorems.Thm_MMSSevenNinths_Main_theorem_8_1
-- name    : MMSSevenNinths.Main.theorem_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:49:32.062077+00:00
-- url     : https://prove2.me/theorems/1ccba159-b7bb-48c3-a811-5e874010be79
-- title:
--   Theorem 8.1 — a complete 7/9-MMS allocation in strongly polynomial time: O(n⁵m⁴) calls to Algorithm 1, O(n⁷m⁵) time
-- statement:
--   For nonnegative additive valuations, a complete $\frac79$-MMS allocation can be computed in strongly polynomial time. Precisely, there are absolute constants $C_1,C_2,C_3,d$ and one fixed LP-free program of the exact register machine (with a designated entry instruction for Algorithm 1 and a block of threshold registers), all chosen before $n$, $m$ and the values, such that for every instance with $n\ge1$ agents, $m\ge0$ goods and nonnegative additive real valuations:
--
--   1. the algorithm (if $n>m$ give all goods to one agent; otherwise build the ordered instance, run the threshold search Algorithm 14 on it, complete the successful call's allocation and convert it back) outputs a complete allocation $\sigma$ with $v_i(B_i)\ge\frac79\mathrm{MMS}_i$ for every agent $i$;
--   2. if $n\le m$ the threshold search terminates (some call of Algorithm 1 succeeds), and the algorithm makes at most $C_1n^5m^4$ calls to Algorithm 1;
--   3. on input $(n,m,(v_i(e_g)))$ the program halts within $C_2(n^7m^5+1)$ executed instructions with $\sigma$ in its output registers; it enters the Algorithm 1 subroutine exactly once per call, the $k$-th time with the $k$-th threshold vector of the search in its threshold registers, and returns at a designated exit with the actual success flag, failed set, partial allocation and failed-agent update values before the next entry or final halt;
--   4. on rational inputs, every register at every one of these steps holds a value of encoding length at most $C_3(L+1)^d$, where $L$ is the input length.
--
--   Differences from the source:
--   - reading: runs in O(n⁷m⁵) time, with each arithmetic operation and numerical comparison taking O(1) time → a bound on the number of executed instructions of an LP-free program of the exact register machine (every instruction counts: arithmetic, comparisons, address arithmetic, loads, stores, jumps); reason: the paper's unit-cost arithmetic model made explicit; counting every instruction is at least as strong as counting arithmetic operations and comparisons
--   - encoding: O(n⁷m⁵) time → C₂·(n⁷·m⁵ + 1) steps; reason: the +1 covers m = 0 (and the constant overhead of reading the input), where n⁷m⁵ = 0; for m ≥ 1 the two are equivalent up to the constant
--   - reading: the algorithm makes O(n⁵m⁴) calls to Algorithm 1 → algorithm1CallCount V ≤ C₁·n⁵·m⁴ for the Lean-defined algorithm, termination when n ≤ m, and actual program entries with the same thresholds paired with returns containing the corresponding Algorithm 1 success flag, failed set, partial allocation and update values before the next entry or halt; reason: entry counts alone do not specify subroutine computation; the return-state contract ties each counted invocation to the actual Algorithm 1 result, with all instructions included in the same time budget
--   - reading: strongly polynomial time → the step bound above, independent of the values, together with an encoding-length bound C₃·(L+1)^d on every register at every step for rational inputs; reason: the definition the paper uses on p. 26: operation count independent of the numbers and polynomial encoding lengths
--   - reading: we then return any complete allocation (n > m) / assign any unallocated goods arbitrarily → every good to agent 0 when n > m; unallocated goods to agent 0 after a successful call; reason: a concrete choice among the arbitrary ones; the theorem is about computing such an allocation
--   - reading: §8.1: scan candidates in increasing order of j when selecting the largest satisfactory index; record every tested bundle for every active agent → the scan tests j = 2, …, |U| ({u_1,u_j}, resp. {u_1,u_j,u_max(j+1,2k+1)}); reductions are tested in the order R₀,R₁,R₂ (resp. R₂, R₃) up to the first applicable one; tail filling tests T = {u_1,u_{k+1},u_{2k+1}} and then each enlarged bag; each test is logged with the active set; reason: the source fixes increasing scan order but leaves the finite range implicit; choose the distinct-good candidates j = 2, …, |U| and log every such test. A satisfactory candidate j = k+1 is in range. At j = 1 the pair repeats u_1 and the triple is {u_1,u_{2k+1}}; neither can change the largest satisfactory index. Beyond |U| the candidates reduce to {u_1}, which is unsatisfactory by the failed R₀ test in the pair branch or the failed pair test in the triple branch. The log is that of this explicitly fixed implementation
--   - encoding: agents N = {1,…,n} with n ≥ 1, goods e_1,…,e_m in the common order → agents Fin n (agent i+1 is i) with hypothesis 0 < n, goods Fin m (e_{g+1} is g); reason: zero-based finite indexing; n ≥ 1 is implicit in the MMS (an n-partition) and in v_i(M)/n; same instances
--   - encoding: an allocation is an n-partition (B_1,…,B_n) of M → an owner map σ : Fin m → Fin n with B_i = bundle σ i; reason: an owner map is exactly a complete, pairwise disjoint labelled partition with possibly empty bundles; same objects
--   - encoding: valuations given to the algorithm → machine input: n, m in natural registers 0, 1 and v_i(e_{g+1}) in real register i·m+g; the integer owner of good g in real register g at halting; call-return data in real registers starting at outBase; reason: a concrete input/output layout using the indirect-access real memory of the published machine; the O(nm+n) return layout fits within the source per-call O(n²m) budget for 1 ≤ n ≤ m
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, Theorem 8.1, printed p. 24 (PDF 27); proof printed p. 26 (PDF 29)

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_DynStochMatching_Reward_RealMachine
import Definitions.Def_MMSSevenNinths_Main_Instance
import Definitions.Def_MMSSevenNinths_Main_OrderedReduction
import Definitions.Def_MMSSevenNinths_Main_Algorithm1
import Definitions.Def_MMSSevenNinths_Main_ThresholdSearch
import Definitions.Def_MMSSevenNinths_Main_Machine

namespace MMSSevenNinths.Main

open DynStochMatching.Reward LittleCharity.MMS

/-- Huang and Zhou (2026), held STOC 2027 submission, Theorem 8.1, printed p. 24 (PDF 27).
For nonnegative additive valuations, a complete 7/9-MMS allocation is computed in strongly
polynomial time: there are absolute constants and one fixed LP-free register-machine program,
chosen before `n`, `m` and the values, such that for every instance with `n ≥ 1` agents
* the full algorithm (`sevenNinthsAllocation`: ordered instance, Algorithm 14, conversion back)
  outputs a complete allocation giving every agent at least `7/9` of her MMS;
* Algorithm 14 terminates (some call succeeds) and makes at most `C₁ n⁵ m⁴` calls to
  Algorithm 1;
* the program halts within `C₂ (n⁷ m⁵ + 1)` steps with that allocation in its output registers,
  enters its Algorithm 1 subroutine (instruction `entry`) exactly once per call, the `k`-th time
  with the `k`-th threshold vector in registers `thrBase + i`, and returns before the next
  entry with the actual success flag, failed set, partial allocation and failed-agent update values;
* on rational inputs every register at every step has encoding length at most
  `C₃ (L + 1)^d`, `L` the input length. -/
theorem theorem_8_1 :
    ∃ C₁ : ℕ, ∃ code : List Instruction, LPFree code ∧ ∃ entry exitPC thrBase outBase C₂ C₃ d : ℕ,
      (∀ (n m : ℕ) (hn : 0 < n) (V : Fin n → Finset (Fin m) → ℝ), IsAdditive V →
        IsApproxMMS (7 / 9 : ℝ) V (sevenNinthsAllocation hn V) ∧
        (n ≤ m → ∃ t, (searchCall (orderedInstance V) t).success = true) ∧
        algorithm1CallCount V ≤ C₁ * n ^ 5 * m ^ 4 ∧
        ∀ O : LinearOracle, ∃ t ≤ C₂ * (n ^ 7 * m ^ 5 + 1),
          Halted code (stateAt O code (machineInput [n, m] (instanceReals V)) t) ∧
          OwnerOutput (stateAt O code (machineInput [n, m] (instanceReals V)) t)
            (sevenNinthsAllocation hn V) ∧
          (visitTimes O code (machineInput [n, m] (instanceReals V)) entry t).length =
            algorithm1CallCount V ∧
          ∀ (k : ℕ) (hk : k < (visitTimes O code (machineInput [n, m] (instanceReals V)) entry t).length),
            (∀ i : Fin n,
              (stateAt O code (machineInput [n, m] (instanceReals V))
                  ((visitTimes O code (machineInput [n, m] (instanceReals V)) entry t)[k])).reals
                  (thrBase + i.val) = thresholdSeq (orderedInstance V) k i) ∧
            ∃ r : ℕ,
              (visitTimes O code (machineInput [n, m] (instanceReals V)) entry t)[k] < r ∧
              r < t ∧
              (stateAt O code (machineInput [n, m] (instanceReals V)) r).pc = exitPC ∧
              CallOutput (stateAt O code (machineInput [n, m] (instanceReals V)) r) outBase
                (orderedInstance V) (thresholdSeq (orderedInstance V) k) ∧
              ∀ (j : ℕ) (hj : j < (visitTimes O code (machineInput [n, m] (instanceReals V)) entry t).length),
                k < j → r < (visitTimes O code (machineInput [n, m] (instanceReals V)) entry t)[j]) ∧
      (∀ (n m : ℕ), 0 < n → ∀ Q : Fin n → Fin m → ℚ, (∀ i g, 0 ≤ Q i g) →
        SizesWithin code (machineInput [n, m] ((ratEntries Q).map (fun q => (q : ℝ))))
          (C₂ * (n ^ 7 * m ^ 5 + 1)) (C₃ * (inputLength [n, m] (ratEntries Q) + 1) ^ d)) := by sorry

end MMSSevenNinths.Main
