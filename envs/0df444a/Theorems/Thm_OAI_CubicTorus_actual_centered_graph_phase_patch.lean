-- Prove2me | Theorems.Thm_OAI_CubicTorus_actual_centered_graph_phase_patch
-- name    : OAI.CubicTorus.actual_centered_graph_phase_patch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:49:48.020786+00:00
-- url     : https://prove2.me/theorems/74bbb901-ecc0-41e0-8fb2-f1ca0253f413
-- title:
--   OAI.CubicTorus.actual_centered_graph_phase_patch: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.actual_centered_graph_phase_patch` of [lean/OAI/Geometry/CubicTorus/Curvature/TorusC2CMCAt.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/TorusC2CMCAt.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem actual_centered_graph_phase_patch {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
--       {n : Cover} {g : Plane → ℝ} {r : ℝ} (hn : ‖n‖=1) (hr : 0 < r)
--       (hg : LipschitzWith (1/4) g) (hg0 : g 0=0)
--       (hgC : ContDiffOn ℝ 1 g (Metric.ball 0 r))
--       (hcover : ∀ x∈Metric.ball (0 : Cover) r,
--         quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
--           normalGraph n g (normalPlaneCoordinates n x)=x) :
--       ∃ (R ρ : ℝ) (U : Set Cover), R < r ∧
--         ‖n‖=1 ∧ LipschitzWith (1/4) g ∧ g 0=0 ∧ 0<R ∧ 0<ρ ∧
--         (∀ y∈Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
--         IsOpen U ∧ Metric.closedBall cubeCenter (2*ρ) ⊆ U ∧
--         U ⊆ Metric.ball cubeCenter R ∧ U ⊆ {x | ∀ i, 0<x i ∧ x i<1} ∧
--         (∀ x∈U, quotientMap x∈frontier (openRepresentative E) ↔
--           normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter) ∧
--         ((∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ graphSignedHeight cubeCenter n g x<0)) ∨
--          (∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n g x)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.Plane`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.graphSignedHeight`, `OAI.CubicTorus.normalGraph`, `OAI.CubicTorus.normalPlaneCoordinates` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical`, `OAI.CubicTorus.Periodic.isMinimizerAt_translation_nodal_count`, `OAI.CubicTorus.TrueRadialTube.exists_revolution_CMC`, `OAI.CubicTorus.first_transition_nonstandard_monotone_revolution`, `OAI.CubicTorus.isMinimizerAt_H1_jacobi_unique_continuation`, `OAI.CubicTorus.isMinimizerAt_axialFluxWeight_pos`, `OAI.CubicTorus.isMinimizerAt_axialHeight_absolutelyContinuous`, `OAI.CubicTorus.isMinimizerAt_axial_boundary_null`, `OAI.CubicTorus.isMinimizerAt_axial_local_cylinder`, `OAI.CubicTorus.isMinimizerAt_center_normal_unique`, `OAI.CubicTorus.isMinimizerAt_centeredJacobiChart`, `OAI.CubicTorus.isMinimizerAt_centered_holder_CMC`, `OAI.CubicTorus.isMinimizerAt_chamber_continuous_exit`, `OAI.CubicTorus.isMinimizerAt_corner_boundary_heights_null`, `OAI.CubicTorus.isMinimizerAt_global_normal`, `OAI.CubicTorus.isMinimizerAt_mean_square_equality_spherical`, `OAI.CubicTorus.isMinimizerAt_nodal_splice_closed`, `OAI.CubicTorus.isMinimizerAt_normal_curvature_nonnegative`, `OAI.CubicTorus.isMinimizerAt_normal_linear_chart`, `OAI.CubicTorus.isMinimizerAt_oriented_CMC_charts`, `OAI.CubicTorus.isMinimizerAt_positive_position_spherical`, `OAI.CubicTorus.isMinimizerAt_radial_slice_length_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor`, `OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign`, `OAI.CubicTorus.isMinimizerAt_rotation_jacobi_from_germs`, `OAI.CubicTorus.isMinimizerAt_smooth_radial_section_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible`, `OAI.CubicTorus.isMinimizerAt_tubular_sections`, `OAI.CubicTorus.isMinimizerAt_two_vertices_smooth_tube`, `OAI.CubicTorus.isMinimizerAt_umbilic_local_sphere`, `OAI.CubicTorus.isMinimizerAt_zero_component_local_cylinder`, `OAI.CubicTorus.isMinimizerAt_zero_component_multiplier_ne_zero`, `OAI.CubicTorus.isMinimizerAt_zero_coordinate_cylindrical`, `OAI.CubicTorus.isMinimizerAt_zero_curvature_local_normal`, `OAI.CubicTorus.isoperimetricProfile_power_upper_support` and `OAI.CubicTorus.normalComponentScalar_global_jacobi` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/TorusC2CMCAt.lean (declaration OAI.CubicTorus.actual_centered_graph_phase_patch)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem actual_centered_graph_phase_patch {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {n : Cover} {g : Plane → ℝ} {r : ℝ} (hn : ‖n‖=1) (hr : 0 < r)
    (hg : LipschitzWith (1/4) g) (hg0 : g 0=0)
    (hgC : ContDiffOn ℝ 1 g (Metric.ball 0 r))
    (hcover : ∀ x∈Metric.ball (0 : Cover) r,
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x) :
    ∃ (R ρ : ℝ) (U : Set Cover), R < r ∧
      ‖n‖=1 ∧ LipschitzWith (1/4) g ∧ g 0=0 ∧ 0<R ∧ 0<ρ ∧
      (∀ y∈Metric.closedBall (0 : Plane) R, ContDiffAt ℝ 1 g y) ∧
      IsOpen U ∧ Metric.closedBall cubeCenter (2*ρ) ⊆ U ∧
      U ⊆ Metric.ball cubeCenter R ∧ U ⊆ {x | ∀ i, 0<x i ∧ x i<1} ∧
      (∀ x∈U, quotientMap x∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n (x-cubeCenter))=x-cubeCenter) ∧
      ((∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ graphSignedHeight cubeCenter n g x<0)) ∨
       (∀ᵐ x : Cover ∂volume, x∈U → (quotientMap x∈E ↔ 0<graphSignedHeight cubeCenter n g x))) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
