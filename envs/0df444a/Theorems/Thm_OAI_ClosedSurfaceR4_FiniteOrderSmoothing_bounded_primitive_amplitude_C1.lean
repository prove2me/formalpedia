-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_bounded_primitive_amplitude_C1
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.bounded_primitive_amplitude_C1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:21:26.932627+00:00
-- url     : https://prove2.me/theorems/4835ab03-b0a2-4d9f-af8b-e971e1b9f038
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.bounded_primitive_amplitude_C1: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.bounded_primitive_amplitude_C1` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/BoundedPrimitiveAmplitude.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/BoundedPrimitiveAmplitude.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing`, with `open Set`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem bounded_primitive_amplitude_C1 (i : ι) (D : ℝ) {k : ℝ} (hk : 0 < k) :
--       ∃ eps C : ℝ, 0 < eps ∧ 1 ≤ C ∧
--         ∀ z : PrimitiveAmplitudeData ι, ‖z‖ ≤ D →
--         primitiveDataOperator z.1 = ContinuousLinearMap.id ℝ TensorFiber →
--         k ≤ z.1.1.1 i z.2 → ∀ z' : PrimitiveAmplitudeData ι, ‖z'-z‖ < eps →
--           (primitiveDataOperator z'.1).IsInvertible ∧
--           0 < primitiveParameterCoefficient i z' ∧
--           ‖primitiveParameterInverse z'‖ ≤ C ∧
--           ‖fderiv ℝ primitiveParameterInverse z'‖ ≤ C ∧
--           |primitiveParameterAmplitude i z'| ≤ C ∧
--           ‖fderiv ℝ (primitiveParameterAmplitude i) z'‖ ≤ C
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeDualAdd` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PrimitiveAmplitudeData` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PrimitiveOperatorData` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeDualNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberSpace` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeGroup` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedDataSpace`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveDataOperator`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveParameterAmplitude`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveParameterCoefficient` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveParameterInverse` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.Plane` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.amplitude_parameter_margin` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/BoundedPrimitiveAmplitude.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.bounded_primitive_amplitude_C1)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedAmplitudeGroup
local instance boundedAmplitudeComplete_r08234a_1 : CompleteSpace TensorFiber := inferInstance
local instance boundedFiberFinite_r08234a_1 : FiniteDimensional ℝ TensorFiber := inferInstance
local instance boundedDualFinite_r08234a_1 : FiniteDimensional ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedCovectorFinite_r08234a_1 : FiniteDimensional ℝ (Plane →L[ℝ] ℝ) := inferInstance
variable {ι : Type*} [Fintype ι]

local instance boundedDualFamilyFinite_r08234a_1 : FiniteDimensional ℝ (ι → TensorFiber →L[ℝ] ℝ) := inferInstance
local instance boundedCovectorFamilyFinite_r08234a_1 : FiniteDimensional ℝ (ι → Plane →L[ℝ] ℝ) := inferInstance
local instance boundedOperatorDataFinite_r08234a_1 : FiniteDimensional ℝ (PrimitiveOperatorData ι) := inferInstance
local instance boundedDataFinite_r08234a_1 : FiniteDimensional ℝ (PrimitiveAmplitudeData ι) := inferInstance
local instance boundedDataProper_r08234a_1 : ProperSpace (PrimitiveAmplitudeData ι) :=
  FiniteDimensional.proper ℝ (PrimitiveAmplitudeData ι)
local instance boundedDataNormed_r08234a_1 : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.boundedDataSpace
theorem bounded_primitive_amplitude_C1 (i : ι) (D : ℝ) {k : ℝ} (hk : 0 < k) :
    ∃ eps C : ℝ, 0 < eps ∧ 1 ≤ C ∧
      ∀ z : PrimitiveAmplitudeData ι, ‖z‖ ≤ D →
      primitiveDataOperator z.1 = ContinuousLinearMap.id ℝ TensorFiber →
      k ≤ z.1.1.1 i z.2 → ∀ z' : PrimitiveAmplitudeData ι, ‖z'-z‖ < eps →
        (primitiveDataOperator z'.1).IsInvertible ∧
        0 < primitiveParameterCoefficient i z' ∧
        ‖primitiveParameterInverse z'‖ ≤ C ∧
        ‖fderiv ℝ primitiveParameterInverse z'‖ ≤ C ∧
        |primitiveParameterAmplitude i z'| ≤ C ∧
        ‖fderiv ℝ (primitiveParameterAmplitude i) z'‖ ≤ C := by
  sorry

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
