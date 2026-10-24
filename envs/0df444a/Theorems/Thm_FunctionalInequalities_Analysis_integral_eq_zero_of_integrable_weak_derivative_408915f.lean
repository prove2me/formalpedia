-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_eq_zero_of_integrable_weak_derivative_408915f
-- name    : FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:16.964821+00:00
-- url     : https://prove2.me/theorems/994b8fa2-58d3-474a-ac46-bc0138ef924d
-- title:
--   Integral Of An Integrable Weak Derivative
-- statement:
--   This statement gives the cutoff lemma used for equation (2.1) and Lemma 2.7 of Letwin (arXiv:2607.24164v1).
--
--   Let f and g be real-valued functions on $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$, and let v∈E. Assume g is a weak directional derivative of f along v, written $\partial_v f=g$, and assume both f and g are integrable with respect to Lebesgue volume. Then
--
--   $$\int_E g(x)\,dx=0.$$
--
--   This is a global zero-mean property for an integrable weak derivative and is reusable as a cutoff argument in weak integration by parts.
--
--   **Formalization Note** No positivity, smoothness, or nonzero-direction assumption is included; the assertion applies to every natural number n and every direction v.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1491-L1607 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section IntegrableWeakDivergence
open MeasureTheory Filter
open scoped ContDiff Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.integral_eq_zero_of_integrable_weak_derivative_408915f {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (hweak : HasWeakDerivAlong f g v)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x, g x ∂volume) = 0 := by sorry
