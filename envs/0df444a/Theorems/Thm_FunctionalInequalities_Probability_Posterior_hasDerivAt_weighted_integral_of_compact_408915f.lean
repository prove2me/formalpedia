-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_hasDerivAt_weighted_integral_of_compact_408915f
-- name    : FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:06:03.213441+00:00
-- url     : https://prove2.me/theorems/cee4273a-c1ad-43f1-b2ea-fce3e258ca8d
-- title:
--   Derivative of a Weighted Tilted Integral
-- statement:
--   This is the compact-support differentiation lemma preceding the posterior expectation formula.
--
--   Let $\mu$ be a probability measure on a topological, measurable, second-countable Borel space $\Omega$, and assume its support is compact. Let $\phi,g:\Omega\to\mathbb R$ be continuous and let $f:\Omega\to\mathbb R$ be measurable. Assume that for some $C\ge0$,
--
--   $$\lVert f(x)\rVert\le C\quad\text{for every }x\in\operatorname{supp}\mu.$$
--
--   Then the map
--
--   $$t\longmapsto\int_\Omega e^{\phi(x)+t g(x)}f(x)\,d\mu(x)$$
--
--   has derivative at $t=0$ equal to
--
--   $$\int_\Omega e^{\phi(x)}g(x)f(x)\,d\mu(x).$$
--
--   This result supplies differentiation under the integral sign for unnormalized compactly supported tilts.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L85-L129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, declaration `FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Covariance

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]

theorem FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact_408915f (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (φ x + t * g x) * f x ∂(μ : Measure Ω))
      (∫ x, Real.exp (φ x) * g x * f x ∂(μ : Measure Ω)) 0 := by sorry
