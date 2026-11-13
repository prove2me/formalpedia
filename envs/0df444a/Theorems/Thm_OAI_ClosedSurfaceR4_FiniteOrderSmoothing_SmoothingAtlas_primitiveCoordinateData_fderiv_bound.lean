-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitiveCoordinateData_fderiv_bound
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_fderiv_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:04.928509+00:00
-- url     : https://prove2.me/theorems/0ed3f340-a77b-4f09-869e-b9d8878b5d49
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_fderiv_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_fderiv_bound` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitiveCoordinateDerivative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitiveCoordinateDerivative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem primitiveCoordinateData_fderiv_bound
--       (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
--       (psi phi : (B.centers × Fin 3) → M → ℝ)
--       (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
--       (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
--       (hQ : ∀ (a : B.centers × Fin 3) (p : M), p ∈ tsupport (B.weight a.1) →
--         ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
--       (u : ∀ p : M, CovariantTwoTensor p)
--       (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--         (fun p => TotalSpace.mk' TensorFiber p (u p)))
--       (i : B.centers) {p : M} (hp : p ∈ tsupport (B.weight i))
--       {D : ℝ} (hD : 0 ≤ D)
--       (hbq : ∀ a, p ∈ tsupport (B.weight a.1) →
--         ‖fderiv ℝ (B.coefficientFrameRead P i a) (chart (i : M) p)‖ ≤ D)
--       (hbw : ∀ a, ‖fderiv ℝ (psi a ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ D)
--       (hbv : ∀ a, p ∈ tsupport (B.weight a.1) →
--         ‖fderiv ℝ (B.phaseCovectorRead i (phi a)) (chart (i : M) p)‖ ≤ D)
--       (hbH : ‖fderiv ℝ (B.tensorFrameRead i u) (chart (i : M) p)‖ ≤ D) :
--       ‖fderiv ℝ (B.primitiveCoordinateData P psi phi u i
--         {a | p ∈ tsupport (B.weight a.1)}) (chart (i : M) p)‖ ≤ D
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base` and `OAI.ClosedSurfaceR4.PhaseMean.Tensor` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PrimitiveAmplitudeData` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PrimitiveOperatorData` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coefficientFrameRead`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseCovectorRead` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coordDerivDataSpace` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorFrameRead` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/PrimitiveCoordinateDerivative.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.primitiveCoordinateData_fderiv_bound)

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
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorSpace
local instance coordDerivFiberT2_r4d49ef_1 : T2Space TensorFiber := inferInstance
local instance coordDerivDualT2_r4d49ef_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorT2_r4d49ef_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivCovectorSpace
local instance coordDerivFiberT2_r4d49ef_2 : T2Space TensorFiber := inferInstance
local instance coordDerivDualT2_r4d49ef_2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorT2_r4d49ef_2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance coordDerivDualAdd_r4d49ef_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordDerivDualSmul
variable (B : SmoothingAtlas M)

local instance coordDerivSectionNormed_r4d49ef_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordDerivSectionSpace_r4d49ef_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance coordDerivDataNormed_r4d49ef_1 : NormedAddCommGroup (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.coordDerivDataSpace
local instance coordDerivDataT2_r4d49ef_1 : T2Space (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
local instance coordDerivDataDualNormed_r4d49ef_1 : NormedAddCommGroup (PrimitiveAmplitudeData (B.centers × Fin 3) →L[ℝ] ℝ) := inferInstance
local instance coordDerivDataDualSpace_r4d49ef_1 : NormedSpace ℝ (PrimitiveAmplitudeData (B.centers × Fin 3) →L[ℝ] ℝ) := inferInstance
theorem primitiveCoordinateData_fderiv_bound
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hQ : ∀ (a : B.centers × Fin 3) (p : M), p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (i : B.centers) {p : M} (hp : p ∈ tsupport (B.weight i))
    {D : ℝ} (hD : 0 ≤ D)
    (hbq : ∀ a, p ∈ tsupport (B.weight a.1) →
      ‖fderiv ℝ (B.coefficientFrameRead P i a) (chart (i : M) p)‖ ≤ D)
    (hbw : ∀ a, ‖fderiv ℝ (psi a ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ D)
    (hbv : ∀ a, p ∈ tsupport (B.weight a.1) →
      ‖fderiv ℝ (B.phaseCovectorRead i (phi a)) (chart (i : M) p)‖ ≤ D)
    (hbH : ‖fderiv ℝ (B.tensorFrameRead i u) (chart (i : M) p)‖ ≤ D) :
    ‖fderiv ℝ (B.primitiveCoordinateData P psi phi u i
      {a | p ∈ tsupport (B.weight a.1)}) (chart (i : M) p)‖ ≤ D := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
