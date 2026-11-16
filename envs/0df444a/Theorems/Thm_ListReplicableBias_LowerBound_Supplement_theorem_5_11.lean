-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_theorem_5_11
-- name    : ListReplicableBias.LowerBound.Supplement.theorem_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:24:20.009829+00:00
-- url     : https://prove2.me/theorems/54116507-d155-4824-aa70-dc147282d6e5
-- title:
--   Theorem 5.11 (= Thm 4.2 = Thm B.3) — Ω(d²/(ε² log k)) samples for k-list replicability
-- statement:
--   There is an absolute constant $c>0$ such that for all $d,k\in\mathbb N$ with $d+1\le k\le2^d$, all $\varepsilon,\delta\in(0,1/8)$, and every randomized adaptive $N$-toss sampling algorithm $A$ that is $(k,\varepsilon,\delta)$-list replicable for the $d$-CoinBiasEstimationProblem,
--   $$N\ge c\,\frac{d^2}{\varepsilon^2\ln k}.$$
--
--   The constant is independent of $d,k,\varepsilon,\delta,N$ and $A$, and there is no dimension threshold. This generalizes the mission's goal (the case $k=d+1$) to every list size between $d+1$ and $2^d$, and with the upper bound of Theorem 6.13 it determines the sample complexity of $k$-list replicable bias estimation up to polylogarithmic factors.
--
--   Differences from the source:
--   - encoding: arbitrary randomized adaptive algorithms with sample access to d coins, using N samples, output in ℝ^d ∪ {⊥} → the published SamplingAlgorithm d N (arbitrary probability seed space, prefix-dependent coin choices, fixed horizon N) with failure as none; reason: the base mission's model of §3.2 and Appendix B; private randomness is in the seed and an algorithm that stops early is padded with ignored tosses, so N is the worst-case toss count
--   - reading: N = Ω(d²/(ε² log k)) with ε, δ fixed first → one constant chosen before every other parameter; reason: the hidden constant cannot depend on ε, which appears inside the bound; the uniform reading is the stronger one
--   - encoding: log k (natural logarithm in the proof) → Real.log of the real cast of k; at d = 0 (k = 1) the Lean bound evaluates to 0; reason: for d ≥ 1 the logarithm is positive; at d = 0 the printed bound d²/(ε² log 1) is undefined
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Theorem 5.11, PDF p. 7 (= Theorem 4.2, PDF p. 3; = Theorem B.3, PDF p. 15)

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Theorem 5.11 (= Theorem 4.2 = Theorem B.3), PDF pp. 7, 3, 15. One absolute
constant c for all d, all k ∈ [d+1, 2^d], all ε, δ ∈ (0, 1/8) and every
randomized adaptive algorithm; no dimension threshold. -/
theorem theorem_5_11 :
    ∃ c : ℝ, 0 < c ∧ ∀ d k : ℕ, d + 1 ≤ k → k ≤ 2 ^ d →
      ∀ ε δ : ℝ, ε ∈ Set.Ioo (0 : ℝ) (1 / 8) → δ ∈ Set.Ioo (0 : ℝ) (1 / 8) →
      ∀ (N : ℕ) (A : SamplingAlgorithm d N), IsListReplicable A k ε δ →
        c * (d : ℝ) ^ 2 / (ε ^ 2 * Real.log (k : ℝ)) ≤ (N : ℝ) := by sorry

end ListReplicableBias.LowerBound.Supplement
