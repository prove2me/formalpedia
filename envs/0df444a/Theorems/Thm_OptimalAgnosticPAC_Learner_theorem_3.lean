-- Prove2me | Theorems.Thm_OptimalAgnosticPAC_Learner_theorem_3
-- name    : OptimalAgnosticPAC.Learner.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:41.758538+00:00
-- url     : https://prove2.me/theorems/eb8cba8f-447d-471d-ac31-893f4f2f76f7
-- title:
--   Theorem 3: the optimal risk bound for the randomized predictor
-- statement:
--   Let $k\ge1$, let $q$ be a symmetric score satisfying (13), and suppose the minimum $L^*=\min_{h\in\mathcal H}L(h)$ is attained. The predictor
--   $$\widehat p(x)=\frac1k\sum_{t=k}^{2k-1}q(x;(Z_1,\dots,Z_t))$$
--   maps into $[-1,1]$, is constructed from $2k-1$ i.i.d. observations and depends on neither $L^*$ nor $\delta$. For every $0<\delta<1$, with probability at least $1-\delta$,
--   $$L(\widehat p)\le L^*+17000\Bigl(\sqrt{\frac{L^*(d+\log(3/\delta))}{k}}+\frac{d+\log(3/\delta)}{k}\Bigr).\tag{18}$$
--   Here $L(\widehat p)$ is the score risk, that is, the risk of the randomized predictor with conditional mean $\widehat p$.
--
--   This is the high probability bound for the randomized learner, before derandomization.
--
--   Differences from the source:
--   - encoding: labels in {−1,+1}, inputs in a set X → labels in Bool with true for +1, signed values through sgn, X : Type; reason: the reused vcDim takes Bool-valued functions on a Type; renaming the two labels changes no quantity
--   - generalization: q is the symmetrized score of §3.1 satisfying (13) → q is any family with IsLOOScore H d q (values in [−1,1], symmetric, jointly measurable, (13)); reason: the paper's proofs use only these properties, and the paper's q is one such family
--   - generalization: VC(H) = d ≥ 1 → vcDim H ≤ d with d ≥ 1; reason: the bound is increasing in d, so taking d = VC(H) gives the source's statement
--   - encoding: with probability at least 1 − δ → the sample law (outer measure) of the failure set is bounded by one minus that level; reason: the two agree on measurable events and the failure bound never overstates the probability
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §3.2, Theorem 3, PDF p. 10 (printed p. 9), with (14) on PDF p. 9

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Learner

/-- Theorem 3, PDF p. 10: the suffix average `p̂` built from `2k - 1` observations maps into
`[-1,1]`, and inequality (18) fails with probability at most `δ`, for every `0 < δ < 1`. -/
theorem theorem_3 {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (hmin : AttainsMinRisk P H)
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ (S : Fin (2 * k - 1) → X × Bool) (x : X), suffixAvg q k S x ∈ Set.Icc (-1 : ℝ) 1) ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      sampleLaw P (2 * k - 1)
        {S | minRisk P H +
              17000 * (Real.sqrt (minRisk P H * ((d : ℝ) + Real.log (3 / δ)) / (k : ℝ)) +
                ((d : ℝ) + Real.log (3 / δ)) / (k : ℝ)) <
            scoreRisk P (suffixAvg q k S)} ≤
        ENNReal.ofReal δ := by sorry

end OptimalAgnosticPAC.Learner
