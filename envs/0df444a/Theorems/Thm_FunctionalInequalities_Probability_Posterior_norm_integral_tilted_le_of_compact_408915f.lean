-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_norm_integral_tilted_le_of_compact_408915f
-- name    : FunctionalInequalities.Probability.Posterior.norm_integral_tilted_le_of_compact_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:29:53.050007+00:00
-- url     : https://prove2.me/theorems/17749582-834c-460c-9706-6d6cf759e261
-- title:
--   Support-Bound Preservation Under Exponential Tilting
-- statement:
--   This statement formalizes the support-bound estimate for tilted expectations in the compact-prior stage of Bizeul–Klartag–Lehec, p. 19.
--
--   Let $\Omega$ be a topological, measurable, Borel, second-countable space, and let $\mu$ be a probability measure with compact support. Let $\varphi:\Omega\to\mathbb R$ be continuous and let $f:\Omega\to\mathbb R$ be measurable. Suppose $C\in\mathbb R$ satisfies $0\leq C$ and
--
--   $$
--   \|f(x)\|\leq C
--   $$
--
--   on the support of $\mu$. Then the integral of $f$ against the exponentially tilted measure is bounded by the same constant:
--
--   $$
--   \left\|\int f\,d(\mu.\operatorname{tilted}\varphi)\right\|\leq C.
--   $$
--
--   This is a finite-valued norm estimate for a tilted probability expectation and is useful for controlling posterior statistics.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L173-L191 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, declaration `FunctionalInequalities.Probability.Posterior.norm_integral_tilted_le_of_compact`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.Posterior.norm_integral_tilted_le_of_compact_408915f (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ f : Ω → ℝ}
    (hφ : Continuous φ) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂((μ : Measure Ω).tilted φ)‖ ≤ C := by sorry
