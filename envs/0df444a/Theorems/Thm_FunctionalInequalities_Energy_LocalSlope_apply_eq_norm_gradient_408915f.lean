-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_eq_norm_gradient_408915f
-- name    : FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:54.519978+00:00
-- url     : https://prove2.me/theorems/285ffb88-7b02-4caf-85ac-80b57240908b
-- title:
--   Local Slope Equals Gradient Norm
-- statement:
--   This is the pointwise identification of the one-moving-point local slope with the canonical Hilbert-space gradient norm.
--
--   Let $E$ be a complete real inner-product normed space, let $f:E\to\mathbb R$, and let $x\in E$. Assume that $f$ is Fréchet differentiable at $x$. Then the local slope `apply` of $f$ at $x$ equals the extended nonnegative real number obtained from the norm of the gradient:
--
--   $$
--   \operatorname{apply}(f,x)=\operatorname{ENNReal.ofReal}\bigl(\|\nabla f(x)\|\bigr).
--   $$
--
--   Here $\nabla f(x)$ is the canonical Hilbert gradient and the right-hand side is an `ENNReal` value in $[0,\infty]$. The Lean declaration is `apply_eq_norm_gradient`; no nontriviality assumption on $E$ or on the derivative is imposed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/LocalSlope/Gradient.lean#L29-L84 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.LocalSlope.Gradient`, declaration `FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient`; the repository is private at upload time).

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

theorem FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient_408915f
    (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    apply f x = ENNReal.ofReal ‖gradient f x‖ := by sorry
