-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PreparedCorrection_exact_correction_initial_displacement
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:51:05.849217+00:00
-- url     : https://prove2.me/theorems/9b0094d9-5de4-4759-8927-794fa410df84
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement` of [lean/OAI/Geometry/SurfaceImmersion/Correction/InitialCorrectionStage.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/InitialCorrectionStage.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`):
--
--   ```lean
--   theorem exact_correction_initial_displacement (c : PreparedCorrection d)
--       (hF : ContMDiff planeModel spaceModel ∞ F) {t P : ℝ}
--       (ht : 0 < t) (htsmall : t ≤ 1/32) (hP : 0 ≤ P)
--       (hmap : d.A.ShiftedBound 2 0 1 P F)
--       (seed : c.Stage t 0)
--       (hseed : seed.map = Real.sqrt (1-(t^(10 : ℝ))^2) • F) :
--       ∃ G : M → Space, IsSmoothIsometricImmersion M g G ∧
--         d.A.WeightedBound 1 2 ((t^(10 : ℝ))^2*P+2*c.ρ*t) (G-F)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CorrectionGeometry`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.Stage` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.IsSmoothIsometricImmersion`, `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_metric_with_property` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/InitialCorrectionStage.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance initialStageFiberNormed_rba22b3_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialStageFiberSpace_rba22b3_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialStageDualAdd_rba22b3_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialStageDualSmul_rba22b3_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection

local instance initialStageFiberNormed_rba22b3_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialStageFiberSpace_rba22b3_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialStageDualAdd_rba22b3_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialStageDualSmul_rba22b3_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialStageSectionNormed_rba22b3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialStageSectionSpace_rba22b3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem exact_correction_initial_displacement (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F) {t P : ℝ}
    (ht : 0 < t) (htsmall : t ≤ 1/32) (hP : 0 ≤ P)
    (hmap : d.A.ShiftedBound 2 0 1 P F)
    (seed : c.Stage t 0)
    (hseed : seed.map = Real.sqrt (1-(t^(10 : ℝ))^2) • F) :
    ∃ G : M → Space, IsSmoothIsometricImmersion M g G ∧
      d.A.WeightedBound 1 2 ((t^(10 : ℝ))^2*P+2*c.ρ*t) (G-F) := by
  sorry

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
