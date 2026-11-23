-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_Supplement_lemma_6
-- name    : MaxSpectralRisk.Duality.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:10:09.396818+00:00
-- url     : https://prove2.me/theorems/f7f6e48a-0a61-44f5-9fdc-ef105d1c3b5d
-- title:
--   Lemma 6 (used in the proof of Theorem 2) — density bounds under weak limits
-- statement:
--   Let $\pi_k,\Theta_k,\pi,\Theta$ be probability measures on a Polish space $\mathcal W$, with $\pi_k\Rightarrow\pi$ and $\Theta_k\Rightarrow\Theta$. Suppose $1\le M<\infty$, $\Theta_k\ll\pi_k$ and $d\Theta_k/d\pi_k\le M$ almost surely for every $k$. Then
--   $$
--   \Theta\ll\pi,\qquad \frac{d\Theta}{d\pi}\le M\quad\pi\text{-a.s.}
--   $$
--   The result preserves the uniform density constraint when the reference measure and the dominated measure both vary.
--
--   Differences from the source:
--   - encoding: Polish W and weak convergence of probability laws → ProbabilityMeasure W with its weak topology and Borel measurable structure; reason: this is precisely narrow convergence; every source product space satisfies the typeclass assumptions
--   - encoding: absolute continuity and density at most M almost surely → explicit absolute continuity and an ENNReal-valued rnDeriv bound by ofReal M; reason: 1 ≤ M makes the real and extended nonnegative bounds identical
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 16, Lemma 6

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Correspondence
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Envelope

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory Filter Topology

/-- Lemma 6, p. 16: both absolute continuity and the finite density bound
survive weak convergence of the two sequences of probability measures. -/
theorem lemma_6 {W : Type*} [TopologicalSpace W] [PolishSpace W]
    [MeasurableSpace W] [BorelSpace W]
    (πs Θs : ℕ → ProbabilityMeasure W) (π Θ : ProbabilityMeasure W)
    (M : ℝ) (hM : 1 ≤ M)
    (hπ : Tendsto πs atTop (𝓝 π)) (hΘ : Tendsto Θs atTop (𝓝 Θ))
    (habs : ∀ k, (Θs k : Measure W) ≪ (πs k : Measure W))
    (hbound : ∀ k, ∀ᵐ w ∂(πs k : Measure W),
      (Θs k : Measure W).rnDeriv (πs k : Measure W) w ≤ ENNReal.ofReal M) :
    (Θ : Measure W) ≪ (π : Measure W) ∧
      ∀ᵐ w ∂(π : Measure W), (Θ : Measure W).rnDeriv (π : Measure W) w ≤
        ENNReal.ofReal M := by sorry

end MaxSpectralRisk.Duality.Supplement
