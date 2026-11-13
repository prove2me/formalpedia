-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_induced_metric_difference_bound
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.induced_metric_difference_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:55:46.715235+00:00
-- url     : https://prove2.me/theorems/0aa12593-e661-4e56-b30d-92a00369124b
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.induced_metric_difference_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.induced_metric_difference_bound` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/InducedMetricDifferenceBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/InducedMetricDifferenceBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem induced_metric_difference_bound (m : ℕ) :
--       ∃ E : ℝ, 0 ≤ E ∧ ∀ (D eps : ℝ), 0 ≤ D → 0 ≤ eps →
--         ∀ F G : M → Space, ContMDiff planeModel spaceModel ∞ F →
--           ContMDiff planeModel spaceModel ∞ G →
--           A.WeightedBound 1 (m+1) D F → A.WeightedBound 1 (m+1) D G →
--           A.WeightedBound 1 (m+1) eps (G-F) →
--           A.TensorWeightedBound 1 m (E*D*eps) (inducedTensor G-inducedTensor F)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inducedTensor` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.metric_frame_tolerance` and `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_induced_metric_read_tolerance` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/InducedMetricDifferenceBound.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.induced_metric_difference_bound)

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

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

variable [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem induced_metric_difference_bound (m : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (D eps : ℝ), 0 ≤ D → 0 ≤ eps →
      ∀ F G : M → Space, ContMDiff planeModel spaceModel ∞ F →
        ContMDiff planeModel spaceModel ∞ G →
        A.WeightedBound 1 (m+1) D F → A.WeightedBound 1 (m+1) D G →
        A.WeightedBound 1 (m+1) eps (G-F) →
        A.TensorWeightedBound 1 m (E*D*eps) (inducedTensor G-inducedTensor F) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
