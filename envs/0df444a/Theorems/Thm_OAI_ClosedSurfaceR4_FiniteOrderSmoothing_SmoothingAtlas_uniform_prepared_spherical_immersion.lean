-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_prepared_spherical_immersion
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T03:08:58.463657+00:00
-- url     : https://prove2.me/theorems/6ee5eac6-141f-4541-894d-56e0924f7d76
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/UniformPreparedSphericalImmersion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/UniformPreparedSphericalImmersion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold`, `open scoped ContDiff Topology Manifold`, `open SphericalJets`):
--
--   ```lean
--   theorem uniform_prepared_spherical_immersion (g : SmoothMetric M) {F : M → Space}
--       (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
--       (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
--       ∃ D c : ℝ, 0 ≤ D ∧ 0 < c ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
--         ∃ (a : P → A.centers) (G : M → Space),
--           (∀ p, A.weight (a p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ G ∧
--           (∀ p, ‖G p‖ = 1) ∧
--           (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
--           A.WeightedBound 1 1 ε (G-F) ∧ A.WeightedBound 1 2 D G ∧
--           (∀ p v, c*g.inner p v v ≤ inducedForm G p v v) ∧
--           ∀ p : P, G p = F p ∧
--             fderiv ℝ (G ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) =
--               fderiv ℝ (F ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) ∧
--             ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (a p : M)).symm)
--               (chartAt Plane (a p : M) p) v w = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.inducedForm` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.SphericalJets.Plane`, `OAI.ClosedSurfaceR4.SphericalJets.Space` and `OAI.ClosedSurfaceR4.SphericalJets.sphericalSecondForm` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_reference_circular_starting_family` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_small_metric_prepared_family` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/UniformPreparedSphericalImmersion.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_prepared_spherical_immersion (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ D c : ℝ, 0 ≤ D ∧ 0 < c ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (a : P → A.centers) (G : M → Space),
        (∀ p, A.weight (a p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ G ∧
        (∀ p, ‖G p‖ = 1) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
        A.WeightedBound 1 1 ε (G-F) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ inducedForm G p v v) ∧
        ∀ p : P, G p = F p ∧
          fderiv ℝ (G ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) =
            fderiv ℝ (F ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (a p : M)).symm)
            (chartAt Plane (a p : M) p) v w = 0 := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
