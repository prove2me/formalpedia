-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_408915f
-- name    : FunctionalInequalities.Analysis.integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:18.968553+00:00
-- url     : https://prove2.me/theorems/84f3dbd4-5f3c-4dcc-b028-3d2a9c4db01b
-- title:
--   Tilted Integration By Parts For Lipschitz Functions
-- statement:
--   This statement establishes weighted integration by parts for a bounded Lipschitz test.
--
--   Let n be a natural number, let U and η be functions on $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$, and let L and Lη be nonnegative-real Lipschitz constants. Assume U is L-Lipschitz, η is Lη-Lipschitz, η is bounded by C in norm, and
--
--   $$\int_E e^{-U(x)}\,dx=1.$$
--
--   For every v∈E, both directional derivatives are integrable with respect to $d\nu=e^{-U}dx$, namely $D_vη$ and $ηD_vU$, and
--
--   $$\int_E D_vη\,d\nu=\int_E η\,D_vU\,d\nu.$$
--
--   This is a reusable first-order integration-by-parts identity for normalized exponential tilts in finite dimensions.
--
--   **Formalization Note** The functions are only assumed globally Lipschitz; the derivatives are Fréchet derivatives where represented by `fderiv`, and the tilted measure uses the potential −U.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean#L235-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian`, declaration `FunctionalInequalities.Analysis.integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped RealInnerProductSpace
section BoundedLipschitzTiltedIBP
open MeasureTheory Filter Set
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz_408915f {n : ℕ}
    {U eta : EuclideanSpace ℝ (Fin n) → ℝ} {L Leta : NNReal}
    (hU : LipschitzWith L U) (heta : LipschitzWith Leta eta)
    (C : ℝ) (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hnorm : (∫ x, Real.exp (-U x) ∂volume) = 1)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => fderiv ℝ eta x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    Integrable (fun x => eta x * fderiv ℝ U x v) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    (∫ x, fderiv ℝ eta x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) =
      ∫ x, eta x * fderiv ℝ U x v ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) := by sorry
