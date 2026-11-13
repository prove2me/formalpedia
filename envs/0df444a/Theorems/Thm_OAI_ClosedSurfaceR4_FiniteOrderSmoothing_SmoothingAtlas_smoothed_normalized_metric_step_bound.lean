-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_smoothed_normalized_metric_step_bound
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smoothed_normalized_metric_step_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:29.752228+00:00
-- url     : https://prove2.me/theorems/2fa99522-aba5-4751-8ffd-fd4035d07026
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smoothed_normalized_metric_step_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smoothed_normalized_metric_step_bound` of [lean/OAI/Geometry/SurfaceImmersion/Correction/GlobalSmoothedMetricStep.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/GlobalSmoothedMetricStep.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`):
--
--   ```lean
--   theorem smoothed_normalized_metric_step_bound (r m : ℕ) :
--       ∃ D E : ℝ, 0 ≤ D ∧ 0 ≤ E ∧
--       ∀ (target : ∀ p : M, CovariantTwoTensor p),
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--           (fun p => TotalSpace.mk' TensorFiber p (target p)) →
--       ∀ (F U : M → Space), ContMDiff planeModel spaceModel ∞ F →
--         ContMDiff planeModel spaceModel ∞ U →
--       ∀ (δ δ' τ s t B C K R : ℝ), δ ≠ 0 → δ' ≠ 0 →
--         0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C → 0 ≤ K →
--         A.InputBound t r B F (normalizedTensorDefect target δ F) →
--         A.InputBound t m C F (normalizedTensorDefect target δ F) →
--         A.WeightedBound τ (m+1) K U →
--         A.TensorWeightedBound τ m R
--           (realizedTensorError target
--             (A.tensorSmooth r s (normalizedTensorDefect target δ F)) δ δ' (A.smooth r s F) U) →
--         A.TensorWeightedBound τ m
--           ((δ'^2)⁻¹ *
--             ((δ^2 + E*K/τ) * (D*tailConstant r*(B*(s/t)^r+C*(τ/t)^r)) + R))
--           (normalizedTensorDefect target δ' (F+U)-target)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tailConstant`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smooth` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smoothStepFiberSpace` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.realizedTensorError` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smoothStepFiberNormed` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.normalizedTensorDefect`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.InputBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_actual_step` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/GlobalSmoothedMetricStep.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smoothed_normalized_metric_step_bound)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smoothStepFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smoothStepFiberSpace
theorem smoothed_normalized_metric_step_bound (r m : ℕ) :
    ∃ D E : ℝ, 0 ≤ D ∧ 0 ≤ E ∧
    ∀ (target : ∀ p : M, CovariantTwoTensor p),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (target p)) →
    ∀ (F U : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ContMDiff planeModel spaceModel ∞ U →
    ∀ (δ δ' τ s t B C K R : ℝ), δ ≠ 0 → δ' ≠ 0 →
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C → 0 ≤ K →
      A.InputBound t r B F (normalizedTensorDefect target δ F) →
      A.InputBound t m C F (normalizedTensorDefect target δ F) →
      A.WeightedBound τ (m+1) K U →
      A.TensorWeightedBound τ m R
        (realizedTensorError target
          (A.tensorSmooth r s (normalizedTensorDefect target δ F)) δ δ' (A.smooth r s F) U) →
      A.TensorWeightedBound τ m
        ((δ'^2)⁻¹ *
          ((δ^2 + E*K/τ) * (D*tailConstant r*(B*(s/t)^r+C*(τ/t)^r)) + R))
        (normalizedTensorDefect target δ' (F+U)-target) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
