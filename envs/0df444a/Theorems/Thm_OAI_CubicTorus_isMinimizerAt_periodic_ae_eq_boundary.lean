-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary
-- name    : OAI.CubicTorus.isMinimizerAt_periodic_ae_eq_boundary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:09:18.977331+00:00
-- url     : https://prove2.me/theorems/9a83b745-5266-4366-9e41-b1f29001871a
-- title:
--   OAI.CubicTorus.isMinimizerAt_periodic_ae_eq_boundary: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_periodic_ae_eq_boundary` of [lean/OAI/Geometry/CubicTorus/Estimates/GraphInverseMetric.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/GraphInverseMetric.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_periodic_ae_eq_boundary {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       {Y : Type*} [TopologicalSpace Y] [T2Space Y]
--       {F G : Cover → Y} (hF : Continuous F) (hG : Continuous G)
--       (hpF : ∀ m x,F (x+latticeVector m)=F x)
--       (hpG : ∀ m x,G (x+latticeVector m)=G x)
--       (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),F z.1=G z.1)
--       (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) : F x=G x
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.latticeVector` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.isMinimizerAt_H1_translation_jacobi`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature`, `OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system`, `OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical`, `OAI.CubicTorus.Periodic.isMinimizerAt_translation_nodal_count`, `OAI.CubicTorus.TrueRadialTube.exists_revolution_CMC`, `OAI.CubicTorus.TrueRadialTube.exists_rotation_zero`, `OAI.CubicTorus.first_transition_nonstandard_monotone_revolution`, `OAI.CubicTorus.isMinimizerAt_axialFluxWeight_pos`, `OAI.CubicTorus.isMinimizerAt_axialHeight_absolutelyContinuous`, `OAI.CubicTorus.isMinimizerAt_axial_boundary_null`, `OAI.CubicTorus.isMinimizerAt_axial_endFlux`, `OAI.CubicTorus.isMinimizerAt_axial_endpoint_perimeter`, `OAI.CubicTorus.isMinimizerAt_axial_local_cylinder`, `OAI.CubicTorus.isMinimizerAt_center_normal_unique`, `OAI.CubicTorus.isMinimizerAt_centeredJacobiChart`, `OAI.CubicTorus.isMinimizerAt_chamber_continuous_exit`, `OAI.CubicTorus.isMinimizerAt_chamber_upper_downset`, `OAI.CubicTorus.isMinimizerAt_connected_curvature_integral_pos`, `OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry`, `OAI.CubicTorus.isMinimizerAt_corner_boundary_heights_null`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_standard`, `OAI.CubicTorus.isMinimizerAt_first_transition_nonstandard_two_vertices`, `OAI.CubicTorus.isMinimizerAt_four_corner_necessary_data`, `OAI.CubicTorus.isMinimizerAt_mean_square_equality_spherical`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound`, `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux`, `OAI.CubicTorus.isMinimizerAt_nonstandard_section_system`, `OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero`, `OAI.CubicTorus.isMinimizerAt_normal_curvature_nonnegative`, `OAI.CubicTorus.isMinimizerAt_normal_linear_chart`, `OAI.CubicTorus.isMinimizerAt_one_vertex_standard_ball`, `OAI.CubicTorus.isMinimizerAt_oriented_CMC_charts`, `OAI.CubicTorus.isMinimizerAt_positive_position_spherical`, `OAI.CubicTorus.isMinimizerAt_radial_slice_length_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor`, `OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign`, `OAI.CubicTorus.isMinimizerAt_rotation_jacobi_from_germs`, `OAI.CubicTorus.isMinimizerAt_second_transition_nonstandard_star`, `OAI.CubicTorus.isMinimizerAt_smaller_side_double_vertices_vacant`, `OAI.CubicTorus.isMinimizerAt_smooth_radial_section_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_strict_two_vertices_impossible`, `OAI.CubicTorus.isMinimizerAt_tubular_sections`, `OAI.CubicTorus.isMinimizerAt_two_missing_vertices_top_flux`, `OAI.CubicTorus.isMinimizerAt_two_vertices_smooth_tube`, `OAI.CubicTorus.isMinimizerAt_umbilic_local_sphere`, `OAI.CubicTorus.isMinimizerAt_zero_component_local_cylinder`, `OAI.CubicTorus.isMinimizerAt_zero_component_multiplier_ne_zero`, `OAI.CubicTorus.isMinimizerAt_zero_coordinate_cylindrical`, `OAI.CubicTorus.isMinimizerAt_zero_curvature_local_normal`, `OAI.CubicTorus.isoperimetricProfile_power_upper_support` and `OAI.CubicTorus.normalComponentScalar_global_jacobi` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/GraphInverseMetric.lean (declaration OAI.CubicTorus.isMinimizerAt_periodic_ae_eq_boundary)

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

theorem isMinimizerAt_periodic_ae_eq_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {F G : Cover → Y} (hF : Continuous F) (hG : Continuous G)
    (hpF : ∀ m x,F (x+latticeVector m)=F x)
    (hpG : ∀ m x,G (x+latticeVector m)=G x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),F z.1=G z.1)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) : F x=G x := by
  sorry

end CubicTorus

end
end

end

end OAI
end
