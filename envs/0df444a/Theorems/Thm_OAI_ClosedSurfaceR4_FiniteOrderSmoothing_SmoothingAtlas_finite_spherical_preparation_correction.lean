-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_spherical_preparation_correction
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T03:09:28.799812+00:00
-- url     : https://prove2.me/theorems/7b446f8e-98c0-4ea0-84b2-f9f5cf134bae
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/FiniteSurfacePreparation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/FiniteSurfacePreparation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Filter Metric Manifold`, `open scoped ContDiff Topology Manifold BigOperators`, `open SphericalJets`):
--
--   ```lean
--   theorem finite_spherical_preparation_correction {F : M → Space}
--       (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
--       ∃ D : ℝ, 0 ≤ D ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
--         ∃ (c : P → A.centers) (Q : M → Space),
--           (∀ p, A.weight (c p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ Q ∧
--           A.WeightedBound 1 1 ε Q ∧ A.WeightedBound 1 2 D Q ∧
--           let G := radialNormalize ∘ (F+Q)
--           ∀ p : P, G p = F p ∧
--             fderiv ℝ (G ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) =
--               fderiv ℝ (F ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) ∧
--             ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (c p : M)).symm)
--               (chartAt Plane (c p : M) p) v w = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.SphericalJets.Plane`, `OAI.ClosedSurfaceR4.SphericalJets.Space`, `OAI.ClosedSurfaceR4.SphericalJets.radialNormalize` and `OAI.ClosedSurfaceR4.SphericalJets.sphericalSecondForm` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_prepared_spherical_immersion` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.uniform_prepared_spherical_immersion` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/FiniteSurfacePreparation.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_spherical_preparation_correction)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
open Set Filter Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem finite_spherical_preparation_correction {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (c : P → A.centers) (Q : M → Space),
        (∀ p, A.weight (c p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ Q ∧
        A.WeightedBound 1 1 ε Q ∧ A.WeightedBound 1 2 D Q ∧
        let G := radialNormalize ∘ (F+Q)
        ∀ p : P, G p = F p ∧
          fderiv ℝ (G ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) =
            fderiv ℝ (F ∘ (chartAt Plane (c p : M)).symm) (chartAt Plane (c p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (c p : M)).symm)
            (chartAt Plane (c p : M) p) v w = 0 := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
