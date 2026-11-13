-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_global_normalized_metric_step_bound
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:52:09.60708+00:00
-- url     : https://prove2.me/theorems/ae9a9e58-6dd4-4ac0-aade-943c16ca42cf
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/GlobalMetricStepBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/GlobalMetricStepBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open WeightedEstimates`):
--
--   ```lean
--   theorem global_normalized_metric_step_bound {target Hs : ∀ p : M, CovariantTwoTensor p}
--       (ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--         (fun p => TotalSpace.mk' TensorFiber p (target p)))
--       (hs : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
--         (fun p => TotalSpace.mk' TensorFiber p (Hs p)))
--       {δ δ' τ BH BE BC : ℝ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0) (hτ : 0 ≤ τ) (m : ℕ)
--       {F G U : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
--       (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U)
--       (hbH : A.TensorWeightedBound τ m BH (normalizedTensorDefect target δ F-Hs))
--       (hbE : A.TensorWeightedBound τ m BE (realizedTensorError target Hs δ δ' G U))
--       (hbC : A.TensorWeightedBound τ m BC (linearMetricTensor (F-G) U)) :
--       A.TensorWeightedBound τ m ((δ'^2)⁻¹*(δ^2*BH+BE+BC))
--         (normalizedTensorDefect target δ' (F+U)-target)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearMetricTensor` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.realizedTensorError` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.normalizedTensorDefect`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundDualSmul`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberNormed`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberSpace` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smoothed_normalized_metric_step_bound` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/GlobalMetricStepBound.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.global_normalized_metric_step_bound)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI006
import Definitions.Def_OAIQ249SI007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundSectionNormed
local instance stepBoundSectionSpace_re26726_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem global_normalized_metric_step_bound {target Hs : ∀ p : M, CovariantTwoTensor p}
    (ht : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    (hs : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (Hs p)))
    {δ δ' τ BH BE BC : ℝ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0) (hτ : 0 ≤ τ) (m : ℕ)
    {F G U : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hG : ContMDiff planeModel spaceModel ∞ G) (hU : ContMDiff planeModel spaceModel ∞ U)
    (hbH : A.TensorWeightedBound τ m BH (normalizedTensorDefect target δ F-Hs))
    (hbE : A.TensorWeightedBound τ m BE (realizedTensorError target Hs δ δ' G U))
    (hbC : A.TensorWeightedBound τ m BC (linearMetricTensor (F-G) U)) :
    A.TensorWeightedBound τ m ((δ'^2)⁻¹*(δ^2*BH+BE+BC))
      (normalizedTensorDefect target δ' (F+U)-target) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
