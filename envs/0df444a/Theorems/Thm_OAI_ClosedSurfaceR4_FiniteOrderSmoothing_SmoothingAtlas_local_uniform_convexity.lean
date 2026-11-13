-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_local_uniform_convexity
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.local_uniform_convexity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:04:20.080801+00:00
-- url     : https://prove2.me/theorems/838e2936-179a-44ce-996d-938ce8d60346
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.local_uniform_convexity: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.local_uniform_convexity` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/LocalUniformConvexity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/LocalUniformConvexity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Manifold`, `open scoped ContDiff Topology`, `open SmallModes PhaseMean PhaseGeometry`):
--
--   ```lean
--   theorem local_uniform_convexity (g : SmoothMetric M) {c C K : ℝ}
--       (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K) (p : M) :
--       ∃ (L : ℝ) (U : Set M), 0 < L ∧ IsOpen U ∧ p ∈ U ∧
--         U ⊆ (coordinateChart p).source ∧
--         ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
--           (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
--           ∀ q ∈ U, ∀ ell : Base, ‖ell‖ ≤ K → ∀ v : Base,
--             (L/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h p)
--               (centeredConvexPhase ell L (coordinateChart p p)) (coordinateChart p q) v v
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.coordinateChart`, `OAI.ClosedSurfaceR4.coordinateMetric`, `OAI.ClosedSurfaceR4.PhaseGeometry.centeredConvexPhase`, `OAI.ClosedSurfaceR4.PhaseGeometry.coordinateMetricHessian` and `OAI.ClosedSurfaceR4.SmallModes.Base` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.isometric_immersion_of_spherical_immersion` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/LocalUniformConvexity.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.local_uniform_convexity)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.PartitionOfUnity
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
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem local_uniform_convexity (g : SmoothMetric M) {c C K : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K) (p : M) :
    ∃ (L : ℝ) (U : Set M), 0 < L ∧ IsOpen U ∧ p ∈ U ∧
      U ⊆ (coordinateChart p).source ∧
      ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
        (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
        ∀ q ∈ U, ∀ ell : Base, ‖ell‖ ≤ K → ∀ v : Base,
          (L/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h p)
            (centeredConvexPhase ell L (coordinateChart p p)) (coordinateChart p q) v v := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
