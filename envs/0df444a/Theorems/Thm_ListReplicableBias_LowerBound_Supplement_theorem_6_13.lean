-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_Supplement_theorem_6_13
-- name    : ListReplicableBias.LowerBound.Supplement.theorem_6_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:30:07.169299+00:00
-- url     : https://prove2.me/theorems/b679070c-d7f6-4c11-bd00-7a978678e579
-- title:
--   Theorem 6.13 (= Thm 4.4) (corrected: d ≥ 2) — a k-list replicable estimator with O((d² log d/(ε² log k)) log²(d/δ)) samples
-- statement:
--   There is an absolute constant $C>0$ such that for all $d,k\in\mathbb N$ with $d\ge2$ and $d+1\le k\le2^d$ and all $\varepsilon,\delta\in(0,1)$ there is a randomized $N$-toss sampling algorithm on $d$ coins that is $(k,\varepsilon,\delta)$-list replicable for the $d$-CoinBiasEstimationProblem and uses
--   $$N\le C\,\frac{d^2\ln d}{\varepsilon^2\ln k}\,\Big(\ln\frac d\delta\Big)^2$$
--   samples.
--
--   Together with Theorem 5.11 this determines the sample complexity of $k$-list replicable bias estimation up to polylogarithmic factors for every $k\in[d+1,2^d]$.
--
--   Differences from the source:
--   - correction: d, k ∈ ℕ with k ∈ [d + 1, 2^d] (including d = 1) → 2 ≤ d; reason: at d = 1 (k = 2) the printed bound d² log d/(ε² log k) · log²(d/δ) is 0, forcing N = 0, but with ε = 0.01 and δ = 0.1 one fixed output law would have to put mass ≥ 0.9 near each of 34 points 0.03 apart in [0, 1], which is impossible
--   - encoding: arbitrary randomized adaptive algorithms with sample access to d coins, using N samples, output in ℝ^d ∪ {⊥} → the published SamplingAlgorithm d N (arbitrary probability seed space, prefix-dependent coin choices, fixed horizon N) with failure as none; reason: the base mission's model of §3.2 and Appendix B; private randomness is in the seed and an algorithm that stops early is padded with ignored tosses, so N is the worst-case toss count
--   - reading: N = O((d² log d/(ε² log k)) log²(d/δ)) with ε, δ fixed first → one constant chosen before every other parameter; reason: the hidden constant cannot depend on ε, which appears inside the bound; the uniform reading is the stronger one
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Theorem 6.13, PDF p. 11 (= Theorem 4.4, PDF p. 4); proof PDF pp. 11–12

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound.Supplement

open ListReplicableBias.LowerBound

/-- Theorem 6.13 (= Theorem 4.4), PDF pp. 11, 4, corrected to d ≥ 2 (at d = 1
the printed bound is 0). C is chosen before d, k, ε, δ; N is the fixed budget. -/
theorem theorem_6_13 :
    ∃ C : ℝ, 0 < C ∧ ∀ d k : ℕ, 2 ≤ d → d + 1 ≤ k → k ≤ 2 ^ d →
      ∀ ε δ : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ (N : ℕ) (A : SamplingAlgorithm d N), IsListReplicable A k ε δ ∧
        (N : ℝ) ≤ C * (d : ℝ) ^ 2 * Real.log (d : ℝ) / (ε ^ 2 * Real.log (k : ℝ)) *
          (Real.log ((d : ℝ) / δ)) ^ 2 := by sorry

end ListReplicableBias.LowerBound.Supplement
