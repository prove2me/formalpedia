-- Prove2me | Theorems.Thm_MemQueryFeas_theorem_2
-- name    : MemQueryFeas.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:41:22.696453+00:00
-- url     : https://prove2.me/theorems/23a33706-a58f-4ca7-9eaa-2d0c1ae66020
-- title:
--   Theorem 2 — propagation of the Block property
-- statement:
--   There are universal constants $C_b>0$ and $c>0$ and a threshold $d_0$ such that the following holds in the setting of §3, for $d\ge d_0$ and $P\ge2$. Let $\Delta\in(0,1]$, fix $p\in\{2,\dots,P\}$, and suppose
--   $$
--   C_b\,\frac{M/N_p+P}{\tilde d}\cdot P\log(d/\Delta)\log P\ \le\ k\ \le\ \frac{\tilde d}{C_bP\log(d/\Delta)\log d}.
--   $$
--   Fix a layer-$(p-1)$ phase $v\in V_{p-1}$ and let $\Delta'\le c\,\frac{\Delta}{k}\big(\frac{\tilde d}{d}\big)^{3/2}$. If $v$ is well-behaved and $R_v$ is $\Delta$-$\mathrm{Block}_k(q\mid\mathrm{Mem}_v,C_v,E_{>p-1})$, then for at least half of the children $w\in V_p$ of $v$, $w$ is well-behaved and $R_w$ is $\Delta'$-$\mathrm{Block}_k(q-\frac1P\mid\mathrm{Mem}_w,C_w,E_{>p})$.
--
--   This is the inductive step of the lower bound: the learner cannot skip most layer-$p$ phases nested in a phase whose region it cannot hit.
--
--   Differences from the source:
--   - reading: d sufficiently large → ∃ d₀, uniform in all other parameters; reason: the usual meaning of the phrase
--   - reading: Theorem 2's constants C_b and c ("universal"; c is introduced on p.13) → ∃ C_b > 0, ∃ c > 0 before d₀ and all other parameters; reason: both are universal constants
--   - reading: the k-condition (involving N_p) printed before "Fix p" → p fixed first; the k-condition is for that p; reason: N_p depends on p; Corollary 1's proof checks the condition for each p ∈ {2,…,P}
--   - encoding: C_b(M/N_p + P)/d̃ · P log(d/Δ) log P ≤ k ≤ d̃/(C_b P log(d/Δ) log d) → C_b(M + P N_p)P log(d/Δ) log P ≤ k d̃ N_p and k C_b P log(d/Δ) log d ≤ d̃; reason: multiplied out; equal for nonzero N_p, d̃, and a zero denominator is read as +∞
--   - reading: a majority of the N_p children → at least half: N_p ≤ 2·#(children with the property); reason: the proof obtains at least half (3/4 + 3/4 − 1 = 1/2)
--   - reading: the fixed deterministic learner of §3 (measurability not stated) → its memory update is Borel measurable in the returned normal (DetMemAlg.IsMeasurable); reason: standing convention: Mem_v must be a random variable for the probabilities and information quantities of §3 to be defined
--   - generalization: Algorithm 4, line 5: an arbitrary separation oracle for Q_{E_1,…,E_P} → an arbitrary final oracle (a function of E_1,…,E_P), not required to be valid; reason: phase memories are fixed before the oracle passes its last leaf, so the final oracle never affects them; a valid final oracle is a special case
--   - encoding: the random construction of Algorithm 2 → an abstract probability space carrying E_1,…,E_P and all versions, with their conditional laws as hypotheses (IsSkeleton); reason: same joint law; the paper's probabilities are probabilities under this law
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Theorem 2, p.11 (PDF p.12); proof pp.27–28

import Mathlib
import Definitions.Def_MemQueryFeas_IsSkeleton
import Definitions.Def_MemQueryFeas_WellBehaved
import Definitions.Def_MemQueryFeas_PhaseBlock
import Definitions.Def_MemQueryFeas_DetMemAlg_IsMeasurable

open MeasureTheory

namespace MemQueryFeas

open Classical in
/-- **Theorem 2 (propagation of `∆-Block_k`).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Theorem 2, p.11 (PDF p.12): "Let `d ≥ 1` be
sufficiently large. Let `P ≥ 2`. There exists a universal constant `C_b > 0` such that the following
holds. Let `∆ ∈ (0, 1]` and suppose that `C_b (M/N_p + P)/d̃ · P log(d/∆) log P ≤ k ≤
d̃/(C_b P log(d/∆) log d)`. Fix `p ∈ {2, . . . , P}` and a layer-`(p − 1)` phase `v ∈ V_{p−1}` and let
`∆′ ≤ c (∆/k) (d̃/d)^{3/2}`. Suppose that `v` is well-behaved and `R_v` is
`∆-Block_k(q | Mem_v, C_v, E_{>p−1})`. Then, for a majority of children `w ∈ V_p` of `v`, `w` is
well-behaved and `R_w` is `∆′-Block_k(q − 1/P | Mem_w, C_w, E_{>p})`."

**Formalization Note.** `C_b` and `c` are universal constants (chosen first; `c` is the second
universal constant of p.13), then `d₀`. The layer `p` is fixed before the condition on `k`, which
involves `N_p`. The `k`-conditions are multiplied out by `d̃ N_p` and by the denominator (a zero
denominator is read as `+∞`). "A majority" is "at least half". The setting is that of §3 (standing
assumptions, a fixed measurable deterministic learner, a skeleton model, any final oracle). log is
base 2. -/
theorem theorem_2 :
    ∃ Cb : ℝ, 0 < Cb ∧ ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(d : ℝ)) → ∀ P : ℕ, 2 ≤ P → P ≤ d →
      ∀ (M : ℕ) (alg : DetMemAlg d M), alg.IsMeasurable →
      ∀ fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d),
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ν : Measure (Op d)) (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d),
        IsSkeleton d ε P μ ν Eb ch →
      ∀ (Δ : ℝ) (k p : ℕ), 0 < Δ → Δ ≤ 1 → 2 ≤ p → p ≤ P →
        Cb * ((M : ℝ) + P * Np d ε P p) * P * Real.logb 2 (d / Δ) * Real.logb 2 P ≤
          (k : ℝ) * dt d P * Np d ε P p →
        (k : ℝ) * (Cb * P * Real.logb 2 (d / Δ) * Real.logb 2 d) ≤ dt d P →
      ∀ v : List ℕ, IsPhase (Np d ε P) (p - 1) v → ∀ Δ' q : ℝ,
        Δ' ≤ c * Δ / k * ((dt d P : ℝ) / d) ^ ((3 : ℝ) / 2) →
        WellBehaved ε P alg fin μ Eb ch v → PhaseBlock ε P alg fin μ Eb ch k Δ q v →
        Np d ε P p ≤ 2 * ((Finset.Icc 1 (Np d ε P p)).filter (fun i =>
          WellBehaved ε P alg fin μ Eb ch (v ++ [i]) ∧
            PhaseBlock ε P alg fin μ Eb ch k Δ' (q - 1 / P) (v ++ [i]))).card := by sorry

end MemQueryFeas
