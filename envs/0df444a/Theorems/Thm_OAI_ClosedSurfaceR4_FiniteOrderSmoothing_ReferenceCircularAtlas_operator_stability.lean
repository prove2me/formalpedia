-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_operator_stability
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.operator_stability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:37:37.050603+00:00
-- url     : https://prove2.me/theorems/e8706d08-38f3-48d9-b0c0-fc058b6841ef
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.operator_stability: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.operator_stability` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceOperatorStability.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceOperatorStability.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas`, with `open Set Manifold`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem operator_stability : ∃ eps : ℝ, 0 < eps ∧
--       ∀ (T : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p)
--         (u : ∀ p : M, CovariantTwoTensor p),
--       (∀ i p, p ∈ tsupport (d.B.weight i) →
--         ‖d.B.tensorOperatorFrame i p (T p)-ContinuousLinearMap.id ℝ TensorFiber‖ < eps) →
--       (∀ i p, p ∈ tsupport (d.B.weight i) →
--         ‖(d.B.tensorTriv i).continuousLinearMapAt ℝ p (u p)-
--           d.chartReference i (chart (i : M) p)‖ < eps) →
--       (∀ p, (T p).IsInvertible) ∧
--         ∀ (a : d.B.centers × Fin 3) p, p ∈ tsupport (d.B.weight a.1) →
--           0 < d.B.primitiveCoefficientField d.basis a p ((T p).inverse (u p))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorOperatorFrame` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoefficientField` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.basis` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.chartReference` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refOperatorDualAdd`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refOperatorFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refOperatorFiberSpace` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.circular_operator_metric_stability` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceOperatorStability.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.operator_stability)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refOperatorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refOperatorFiberSpace
local instance refOperatorDualSmul_r7f14bc_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

 attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.refOperatorFiberNormed
local instance refOperatorSectionNormed_r7f14bc_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance refOperatorSectionSpace_r7f14bc_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem operator_stability : ∃ eps : ℝ, 0 < eps ∧
    ∀ (T : ∀ p : M, CovariantTwoTensor p →L[ℝ] CovariantTwoTensor p)
      (u : ∀ p : M, CovariantTwoTensor p),
    (∀ i p, p ∈ tsupport (d.B.weight i) →
      ‖d.B.tensorOperatorFrame i p (T p)-ContinuousLinearMap.id ℝ TensorFiber‖ < eps) →
    (∀ i p, p ∈ tsupport (d.B.weight i) →
      ‖(d.B.tensorTriv i).continuousLinearMapAt ℝ p (u p)-
        d.chartReference i (chart (i : M) p)‖ < eps) →
    (∀ p, (T p).IsInvertible) ∧
      ∀ (a : d.B.centers × Fin 3) p, p ∈ tsupport (d.B.weight a.1) →
        0 < d.B.primitiveCoefficientField d.basis a p ((T p).inverse (u p)) := by
  sorry

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
