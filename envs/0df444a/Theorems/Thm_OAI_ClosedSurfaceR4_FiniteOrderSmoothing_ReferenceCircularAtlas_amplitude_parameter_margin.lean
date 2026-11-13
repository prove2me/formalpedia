-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_amplitude_parameter_margin
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.amplitude_parameter_margin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:37:07.813548+00:00
-- url     : https://prove2.me/theorems/081bbae3-78f8-435f-8ece-83430fab12ce
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.amplitude_parameter_margin: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.amplitude_parameter_margin` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceAmplitudeMargin.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceAmplitudeMargin.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas`, with `open Set Manifold`, `open scoped ContDiff Topology BigOperators`):
--
--   ```lean
--   theorem amplitude_parameter_margin : ∃ eps R : ℝ, 0 < eps ∧ 1 ≤ R ∧
--       ∀ i p, p ∈ tsupport (d.B.weight i) → ∀ a : d.B.centers × Fin 3,
--         p ∈ tsupport (d.B.weight a.1) → ∀ z : PrimitiveAmplitudeData (d.B.centers × Fin 3),
--         ‖z-d.coordinateReference i p‖ < eps →
--           (primitiveDataOperator z.1).IsInvertible ∧
--           0 < primitiveParameterCoefficient a z ∧
--           |primitiveParameterAmplitude a z| ≤ R ∧
--           ‖fderiv ℝ (primitiveParameterAmplitude a) z‖ ≤ R
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.dataDualAdd` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PrimitiveAmplitudeData` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PrimitiveOperatorData` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveDataOperator`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveParameterAmplitude` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveParameterCoefficient` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.coordinateReference` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeMarginFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeMarginFiberSpace` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.actual_amplitude_parameter_bound` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/ReferenceAmplitudeMargin.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.amplitude_parameter_margin)

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
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeMarginFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.amplitudeMarginFiberSpace
theorem amplitude_parameter_margin : ∃ eps R : ℝ, 0 < eps ∧ 1 ≤ R ∧
    ∀ i p, p ∈ tsupport (d.B.weight i) → ∀ a : d.B.centers × Fin 3,
      p ∈ tsupport (d.B.weight a.1) → ∀ z : PrimitiveAmplitudeData (d.B.centers × Fin 3),
      ‖z-d.coordinateReference i p‖ < eps →
        (primitiveDataOperator z.1).IsInvertible ∧
        0 < primitiveParameterCoefficient a z ∧
        |primitiveParameterAmplitude a z| ≤ R ∧
        ‖fderiv ℝ (primitiveParameterAmplitude a) z‖ ≤ R := by
  sorry

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
