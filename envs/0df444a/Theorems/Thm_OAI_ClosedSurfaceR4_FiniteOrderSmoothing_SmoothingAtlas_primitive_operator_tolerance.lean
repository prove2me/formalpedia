-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitive_operator_tolerance
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:33:37.253026+00:00
-- url     : https://prove2.me/theorems/40558e4c-a313-4cf7-8ef6-194d81f8e8b0
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/ActualOperatorTolerance.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ActualOperatorTolerance.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold`, `open scoped ContDiff Topology BigOperators`):
--
--   ```lean
--   theorem primitive_operator_tolerance
--       (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
--       (hQ : ∀ (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight a.1) →
--         ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
--       (phi₀ : (B.centers × Fin 3) → M → ℝ)
--       (hphi₀ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi₀ a))
--       {eta : ℝ} (heta : 0 < eta) :
--       ∃ eps : ℝ, 0 < eps ∧ ∀ psi phi : (B.centers × Fin 3) → M → ℝ,
--         (∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1)) →
--         (∀ a p, |psi a p-B.weight a.1 p| < eps) →
--         (∀ (i : B.centers) (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight i) → p ∈ tsupport (B.weight a.1) →
--           ‖B.covectorFrame i p (B.primitivePhaseCovector phi a p)-
--             B.covectorFrame i p (B.primitivePhaseCovector phi₀ a p)‖ < eps) →
--         ∀ i p, p ∈ tsupport (B.weight i) →
--           ‖B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p)-
--             B.tensorOperatorFrame i p
--               (B.primitiveFullOperator P (fun a => B.weight a.1) phi₀ p)‖ < eta
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base` and `OAI.ClosedSurfaceR4.PhaseMean.Tensor` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.covectorFrame`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitivePhaseCovector` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorOperatorFrame` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualToleranceFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualToleranceFiberSpace` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveFullOperator` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.circular_operator_metric_stability` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ActualOperatorTolerance.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitive_operator_tolerance)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualToleranceFiberSpace
local instance actualToleranceDualAdd_rf39c59_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualToleranceDualSmul_rf39c59_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualToleranceFiberNormed
local instance actualToleranceSectionNormed_rf39c59_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance actualToleranceSectionSpace_rf39c59_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem primitive_operator_tolerance
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (hQ : ∀ (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (phi₀ : (B.centers × Fin 3) → M → ℝ)
    (hphi₀ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi₀ a))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ psi phi : (B.centers × Fin 3) → M → ℝ,
      (∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1)) →
      (∀ a p, |psi a p-B.weight a.1 p| < eps) →
      (∀ (i : B.centers) (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight i) → p ∈ tsupport (B.weight a.1) →
        ‖B.covectorFrame i p (B.primitivePhaseCovector phi a p)-
          B.covectorFrame i p (B.primitivePhaseCovector phi₀ a p)‖ < eps) →
      ∀ i p, p ∈ tsupport (B.weight i) →
        ‖B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p)-
          B.tensorOperatorFrame i p
            (B.primitiveFullOperator P (fun a => B.weight a.1) phi₀ p)‖ < eta := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
