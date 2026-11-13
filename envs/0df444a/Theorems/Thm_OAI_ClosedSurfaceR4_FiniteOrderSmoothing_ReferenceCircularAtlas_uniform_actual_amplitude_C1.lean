-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_uniform_actual_amplitude_C1
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:08:21.787025+00:00
-- url     : https://prove2.me/theorems/06bba858-65dc-499b-9985-b65ba25ea116
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/UniformActualAmplitudeC1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/UniformActualAmplitudeC1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem uniform_actual_amplitude_C1 {F : M → Space}
--       (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
--       (href : gref.inner = g.inner-inducedTensor (r • F)) :
--       ∃ pt wt mt : ℝ, 0 < pt ∧ 0 < wt ∧ 0 < mt ∧
--         ∀ Dw Du : ℝ, 0 ≤ Dw → 0 ≤ Du → ∃ E : ℝ, 1 ≤ E ∧
--         ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
--         (∀ i j, ‖ell i j-(d.P i).ξ j‖ < pt) →
--         (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
--         (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
--         (∀ a p, |psi a p-d.B.weight a.1 p| < wt) →
--         (∀ a, d.B.WeightedBound 1 1 Dw (psi a)) →
--         ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
--         A.WeightedBound 1 1 mt (G-F) →
--         d.B.TensorWeightedBound 1 1 Du (g.inner-inducedTensor (r • G)) →
--         ∀ i a p, p ∈ tsupport (d.B.weight i) →
--         let amp := d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
--           (g.inner-inducedTensor (r • G)) a
--         |amp p| ≤ E ∧ ‖fderiv ℝ (amp ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ E
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart` and `OAI.ClosedSurfaceR4.JetPolynomial.Base` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor` and `OAI.ClosedSurfaceR4.SmallModes.Base` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.basis` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.perturbedPhases` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.correctedPrimitiveAmplitude` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` and `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_corrected_term_C1` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/UniformActualAmplitudeC1.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1)

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
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011

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
local instance actualC1FiberNormed_r2e3790_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance actualC1FiberSpace_r2e3790_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance actualC1TensorDualNormed_r2e3790_1 : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1TensorDualSpace_r2e3790_1 : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorNormed_r2e3790_1 : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorSpace_r2e3790_1 : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1FiberT2_r2e3790_1 : T2Space TensorFiber := inferInstance
local instance actualC1TensorDualT2_r2e3790_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorT2_r2e3790_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1DataNormed_r2e3790_1 (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance actualC1DataSpace_r2e3790_1 (ι : Type*) [Fintype ι] : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance
local instance actualC1DataT2_r2e3790_1 (ι : Type*) [Fintype ι] : T2Space (PrimitiveAmplitudeData ι) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
local instance actualC1FiberNormed_r2e3790_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance actualC1FiberSpace_r2e3790_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance actualC1TensorDualNormed_r2e3790_2 : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1TensorDualSpace_r2e3790_2 : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorNormed_r2e3790_2 : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorSpace_r2e3790_2 : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1FiberT2_r2e3790_2 : T2Space TensorFiber := inferInstance
local instance actualC1TensorDualT2_r2e3790_2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorT2_r2e3790_2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1DataNormed_r2e3790_2 (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
local instance actualC1DataSpace_r2e3790_2 (ι : Type*) [Fintype ι] : NormedSpace ℝ (PrimitiveAmplitudeData ι) := inferInstance
local instance actualC1DataT2_r2e3790_2 (ι : Type*) [Fintype ι] : T2Space (PrimitiveAmplitudeData ι) := inferInstance
local instance actualC1DataDualNormed_r2e3790_1 (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance actualC1DataDualSpace_r2e3790_1 (ι : Type*) [Fintype ι] : NormedSpace ℝ (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance actualC1DualAdd_r2e3790_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualC1DualSmul_r2e3790_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance actualC1SectionNormed_r2e3790_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance actualC1SectionSpace_r2e3790_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_actual_amplitude_C1 {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) :
    ∃ pt wt mt : ℝ, 0 < pt ∧ 0 < wt ∧ 0 < mt ∧
      ∀ Dw Du : ℝ, 0 ≤ Dw → 0 ≤ Du → ∃ E : ℝ, 1 ≤ E ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < pt) →
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
      (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < wt) →
      (∀ a, d.B.WeightedBound 1 1 Dw (psi a)) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mt (G-F) →
      d.B.TensorWeightedBound 1 1 Du (g.inner-inducedTensor (r • G)) →
      ∀ i a p, p ∈ tsupport (d.B.weight i) →
      let amp := d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
        (g.inner-inducedTensor (r • G)) a
      |amp p| ≤ E ∧ ‖fderiv ℝ (amp ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ E := by
  sorry

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
