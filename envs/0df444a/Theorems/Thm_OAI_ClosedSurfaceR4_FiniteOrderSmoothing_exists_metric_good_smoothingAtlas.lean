-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_metric_good_smoothingAtlas
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_metric_good_smoothingAtlas
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:37:40.33868+00:00
-- url     : https://prove2.me/theorems/61c2ebb7-3ca2-4a5d-a78c-f5fb73cdeda7
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_metric_good_smoothingAtlas: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_metric_good_smoothingAtlas` of [lean/OAI/Geometry/SurfaceImmersion/Correction/MetricGoodSmoothingAtlas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/MetricGoodSmoothingAtlas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open SmallModes RealModes PhaseGeometry`, `open JetPolynomial.Perturbation (modeSupport)`):
--
--   ```lean
--   theorem exists_metric_good_smoothingAtlas (g : SmoothMetric M) {F : M → Space}
--       (hF : ContMDiff planeModel spaceModel ∞ F)
--       (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
--       (hB : ∀ p, ∃ v w : SmallModes.Base,
--         realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0) :
--       ∃ (A : SmoothingAtlas M)
--         (P : ∀ p, PhasePatch F (coordinateMetric g p) p),
--         (∀ i : A.centers, tsupport (A.weight i) ⊆ (P (i : M)).V) ∧
--         (∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1)) ∧
--         ∀ (i : A.centers) (x : SmallModes.Base),
--           x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
--           Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ∧
--           (∀ j, 0 < (P (i : M)).phaseBasis.Q j (A.tensorPlaneRead i g.inner x)) ∧
--           (∀ j, Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
--             ((P (i : M)).phaseBasis.ξ j)) ∧
--           (∀ j k, j ≠ k →
--             Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
--               ((P (i : M)).phaseBasis.ξ j + (P (i : M)).phaseBasis.ξ k) ∧
--             Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
--               ((P (i : M)).phaseBasis.ξ j - (P (i : M)).phaseBasis.ξ k))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.coordinateMap`, `OAI.ClosedSurfaceR4.coordinateMetric`, `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondForm`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.coordinateCenter` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.PhasePatch` and `OAI.ClosedSurfaceR4.PhasePatch.phaseBasis` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRead` and `OAI.ClosedSurfaceR4.PhaseGeometry.PhaseBasis` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.nonempty` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/MetricGoodSmoothingAtlas.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_metric_good_smoothingAtlas)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial.Perturbation (modeSupport)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

local instance metricGoodFiberNormed_r458a59_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricGoodFiberSpace_r458a59_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricGoodDualAdd_r458a59_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricGoodDualSmul_r458a59_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricGoodSectionNormed_r458a59_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricGoodSectionSpace_r458a59_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem exists_metric_good_smoothingAtlas (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (hB : ∀ p, ∃ v w : SmallModes.Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0) :
    ∃ (A : SmoothingAtlas M)
      (P : ∀ p, PhasePatch F (coordinateMetric g p) p),
      (∀ i : A.centers, tsupport (A.weight i) ⊆ (P (i : M)).V) ∧
      (∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1)) ∧
      ∀ (i : A.centers) (x : SmallModes.Base),
        x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ∧
        (∀ j, 0 < (P (i : M)).phaseBasis.Q j (A.tensorPlaneRead i g.inner x)) ∧
        (∀ j, Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
          ((P (i : M)).phaseBasis.ξ j)) ∧
        (∀ j k, j ≠ k →
          Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
            ((P (i : M)).phaseBasis.ξ j + (P (i : M)).phaseBasis.ξ k) ∧
          Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
            ((P (i : M)).phaseBasis.ξ j - (P (i : M)).phaseBasis.ξ k)) := by
  sorry

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
