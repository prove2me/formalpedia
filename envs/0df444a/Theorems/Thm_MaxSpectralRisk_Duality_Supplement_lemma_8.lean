-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_Supplement_lemma_8
-- name    : MaxSpectralRisk.Duality.Supplement.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:12:02.432353+00:00
-- url     : https://prove2.me/theorems/685ac3d4-576b-45fb-a780-ae4b34aae32d
-- title:
--   Lemma 8 (used in the proof of Theorem 2) — approximation for continuous densities
-- statement:
--   Fix $\alpha\in(0,1)$. Let $\pi_k\Rightarrow\pi$ be weakly convergent probability measures on a Polish space, let $\Theta\in G_\alpha(\pi)$, and suppose $d\Theta/d\pi$ has a bounded continuous version. Then
--   $$
--   \exists(\Theta_k)_{k\ge0},\qquad \Theta_k\in G_\alpha(\pi_k)\text{ for every }k,
--   \qquad\Theta_k\Rightarrow\Theta.
--   $$
--   This approximation result handles the continuous-density case needed for lower hemicontinuity.
--
--   Differences from the source:
--   - encoding: Polish W and weak convergence of probability laws → ProbabilityMeasure W with its weak topology and Borel measurable structure; reason: this is precisely narrow convergence; every source product space satisfies the typeclass assumptions
--   - encoding: Theta in G_alpha(pi) with a bounded continuous version of its density → finite setwise domination and a nonnegative-a.e. BoundedContinuousFunction whose ofReal equals rnDeriv a.e.; reason: finite-measure Radon–Nikodym theory gives the same envelope and continuous density versions; nonnegativity is inherent to a density
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 17, Lemma 8

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Correspondence
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Envelope

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory Filter Topology

/-- Lemma 8, p. 17: a bounded continuous version of the density gives
approximants in every envelope of the converging sequence, not just eventually. -/
theorem lemma_8 {W : Type*} [TopologicalSpace W] [PolishSpace W]
    [MeasurableSpace W] [BorelSpace W]
    (α : ℝ) (hα : 0 < α ∧ α < 1)
    (πs : ℕ → ProbabilityMeasure W) (π Θ : ProbabilityMeasure W)
    (hπ : Tendsto πs atTop (𝓝 π)) (hΘ : Θ ∈ Galpha α π)
    (hη : ∃ η : BoundedContinuousFunction W ℝ, ∀ᵐ w ∂(π : Measure W),
      0 ≤ η w ∧ ENNReal.ofReal (η w) = (Θ : Measure W).rnDeriv (π : Measure W) w) :
    ∃ Θs : ℕ → ProbabilityMeasure W, (∀ k, Θs k ∈ Galpha α (πs k)) ∧
      Tendsto Θs atTop (𝓝 Θ) := by sorry

end MaxSpectralRisk.Duality.Supplement
