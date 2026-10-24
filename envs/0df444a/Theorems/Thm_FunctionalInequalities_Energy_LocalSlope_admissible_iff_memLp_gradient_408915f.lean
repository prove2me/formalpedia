-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_admissible_iff_memLp_gradient_408915f
-- name    : FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:55.207471+00:00
-- url     : https://prove2.me/theorems/06062a83-4b90-48fa-b5a4-ad66c489414b
-- title:
--   Admissibility Characterized By Function And Gradient $L^2$ Membership
-- statement:
--   This theorem characterizes the existing local-slope admissibility predicate in finite-dimensional Euclidean space.
--
--   Let $E$ be a finite-dimensional complete real inner-product normed space with its Borel measurable structure and second-countable topology. Let $\nu$ be a probability measure on $E$, let $m$ be an additive Haar measure, and assume
--
--   $$
--   \nu\ll m.
--   $$
--
--   For every function $f:E\to\mathbb R$, admissibility with respect to $\nu$ is equivalent to the conjunction of local Lipschitz regularity, square-integrability of $f$, and square-integrability of its gradient:
--
--   $$
--   \operatorname{Admissible}(\nu,f)
--   \iff
--   \operatorname{LocallyLipschitz}(f)\;\land\; f\in L^2(\nu)\;\land\;\nabla f\in L^2(\nu).
--   $$
--
--   The Lean declaration is `admissible_iff_memLp_gradient`. The two $L^2$ conditions are expressed by `MemLp` with exponent $2$; the conclusion is an iff, not merely an implication. The associated gradient energy may take values in $[0,\infty]$, while the displayed $L^2$ membership condition requires finiteness.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/LocalSlope/Gradient.lean#L113-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.LocalSlope.Gradient`, declaration `FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [sct : SecondCountableTopology E]
  [FiniteDimensional ℝ E] (ν : ProbabilityMeasure E) (m : Measure E)
  [Measure.IsAddHaarMeasure m]

theorem FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient_408915f (hν : (ν : Measure E) ≪ m) (f : E → ℝ) :
    Admissible ν f ↔
      LocallyLipschitz f ∧ MemLp f 2 (ν : Measure E) ∧ MemLp (gradient f) 2 (ν : Measure E) := by sorry
