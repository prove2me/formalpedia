-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_normal_margin
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:43:02.243433+00:00
-- url     : https://prove2.me/theorems/be28434a-8537-421c-9faf-6b6e37bd39ab
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/AtlasPhaseNormalMargin.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/AtlasPhaseNormalMargin.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold`, `open scoped ContDiff Manifold Topology`, `open JetPolynomial RealModes SurfaceVelocityFamily.Loop`):
--
--   ```lean
--   theorem phase_normal_margin (i : A.centers)
--       (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
--       (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
--       (hcover : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source) :
--       ∃ D : ℝ, 0 < D ∧ ∀ (V : M → Space), ContMDiff planeModel spaceModel ∞ V →
--         ∀ x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base), ∀ c : ℝ, 0 < c →
--           (let J := primitiveNormalTriple (A.vectorChartRead i V ∘ e.symm) (e x)
--            NormalFrame.gramDet (J 0) (J 1) ≠ 0 ∧ c < ‖realNormalPart (J 0) (J 1) (J 2)‖) →
--           Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i V)
--             (planeCoordinateIsometry x)) ∧
--           c/D < ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i V)
--             (planeCoordinateIsometry x)‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.planeCoordinateIsometry`, `OAI.ClosedSurfaceR4.JetVelocityCoordinates.Euclidean`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realNormalPart`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorChartRead` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.VelocityFrame.NormalTriple` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.primitiveNormalTriple` (definitions bundle `OAIQ249SI009` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/AtlasPhaseNormalMargin.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin)

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
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_normal_margin (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hcover : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source) :
    ∃ D : ℝ, 0 < D ∧ ∀ (V : M → Space), ContMDiff planeModel spaceModel ∞ V →
      ∀ x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base), ∀ c : ℝ, 0 < c →
        (let J := primitiveNormalTriple (A.vectorChartRead i V ∘ e.symm) (e x)
         NormalFrame.gramDet (J 0) (J 1) ≠ 0 ∧ c < ‖realNormalPart (J 0) (J 1) (J 2)‖) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i V)
          (planeCoordinateIsometry x)) ∧
        c/D < ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i V)
          (planeCoordinateIsometry x)‖ := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
