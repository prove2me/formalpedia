-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_primitive_atlas_normal_margin
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_primitive_atlas_normal_margin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:51:00.678193+00:00
-- url     : https://prove2.me/theorems/4c1c3057-2b54-4a44-bcae-4d0b9362debf
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_primitive_atlas_normal_margin (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_primitive_atlas_normal_margin` of [lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentPrimitiveNormalMargin.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentPrimitiveNormalMargin.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, with `open Set Manifold`, `open scoped ContDiff Manifold Topology BigOperators`, `open SmallModes RealModes PhaseGeometry JetPolynomial JetPolynomial.Perturbation`):
--
--   ```lean
--   theorem independent_primitive_atlas_normal_margin (data : MetricGoodPhaseData g F) (B : SmoothingAtlas M)
--       (houter : ∀ i x, x ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 x] (fun _ => 1))
--       (hF : ContMDiff planeModel spaceModel ∞ F) (i : B.centers) {c : ℝ} (hc : 0 < c) :
--       ∃ ρ c₀ : ℝ, 0 < ρ ∧ 0 < c₀ ∧
--         ∀ (G V : M → Space), ContMDiff planeModel spaceModel ∞ G →
--           ContMDiff planeModel spaceModel ∞ V →
--         (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) →
--         ∀ b : ℝ, 0 ≤ b → b < ρ → B.WeightedBound 1 2 b (G-F) →
--         (∀ p ∈ tsupport (B.weight i),
--           c < ‖realSecondTensor (spaceCoordinates ∘ B.vectorPlaneRead i V)
--             (planeCoordinateIsometry (chart (i : M) p))‖) →
--         (∀ p ∉ tsupport (B.weight i), V =ᶠ[𝓝 p] G) →
--         ∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
--           c₀ < ‖realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chart`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Primitive/IndependentPrimitiveNormalMargin.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_primitive_atlas_normal_margin)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

theorem independent_primitive_atlas_normal_margin (data : MetricGoodPhaseData g F) (B : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (i : B.centers) {c : ℝ} (hc : 0 < c) :
    ∃ ρ c₀ : ℝ, 0 < ρ ∧ 0 < c₀ ∧
      ∀ (G V : M → Space), ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel spaceModel ∞ V →
      (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) →
      ∀ b : ℝ, 0 ≤ b → b < ρ → B.WeightedBound 1 2 b (G-F) →
      (∀ p ∈ tsupport (B.weight i),
        c < ‖realSecondTensor (spaceCoordinates ∘ B.vectorPlaneRead i V)
          (planeCoordinateIsometry (chart (i : M) p))‖) →
      (∀ p ∉ tsupport (B.weight i), V =ᶠ[𝓝 p] G) →
      ∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
        c₀ < ‖realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖ := by
  sorry

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
