-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_expectation_hasDerivAt_of_compact_408915f
-- name    : FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:07:57.115508+00:00
-- url     : https://prove2.me/theorems/b4b4ceff-381e-4712-bf6c-7277f03f47e6
-- title:
--   First Variation of a Compact Tilted Expectation
-- statement:
--   This formalizes the compact-prior first-variation statement related to Equation (67) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Equation (67), p. 19.
--
--   Let $\mu$ be a probability measure on a topological, measurable, second-countable Borel space with compact support. Let $\phi,g$ be continuous and let $f$ be measurable. Assume that for some $C\ge0$, $\lVert f(x)\rVert\le C$ on $\operatorname{supp}\mu$. For the tilted probability measure with exponent $\phi+t g$, the expectation satisfies
--
--   $$\left.\frac{d}{dt}\right|_{t=0}\int f\,d\bigl(\mu.\operatorname{tilted}(\phi+t g)\bigr)
--   =\operatorname{Cov}_{\mu.\operatorname{tilted}(\phi)}(f,g).$$
--
--   The notation `Measure.tilted` denotes the normalized exponential tilt. This lemma is the basic first-variation formula for compact posterior measures.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L131-L171 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, declaration `FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact_408915f (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, f x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
      (covariance f g ((μ : Measure Ω).tilted φ)) 0 := by sorry
