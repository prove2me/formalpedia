-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
-- name    : OAI.CubicTorus.isMinimizerAt_openRepresentative_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:07:37.684349+00:00
-- url     : https://prove2.me/theorems/40a82757-e9a6-4565-935c-799f09b68716
-- title:
--   OAI.CubicTorus.isMinimizerAt_openRepresentative_ae: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_openRepresentative_ae` of [lean/OAI/Geometry/CubicTorus/Estimates/BVRadial.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVRadial.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_openRepresentative_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       openRepresentative E =ᵐ[torusVolume] E
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_C1_modulus`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_lipschitz_graph`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_field`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_circle_phase`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_standard_slab`, `OAI.CubicTorus.Periodic.isMinimizerAt_connected_or_zero_curvature`, `OAI.CubicTorus.Periodic.isMinimizerAt_full_jacobi_system`, `OAI.CubicTorus.Periodic.isMinimizerAt_normal_support_jets`, `OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical`, `OAI.CubicTorus.Periodic.isMinimizerAt_translation_nodal_count`, `OAI.CubicTorus.TrueRadialTube.exists_rotation_zero`, `OAI.CubicTorus.TrueRadialTube.revolution_area_le_perimeter`, `OAI.CubicTorus.actual_centered_graph_phase_patch`, `OAI.CubicTorus.actual_primary_fixed_scale_packets`, `OAI.CubicTorus.actual_primary_offvertex_C1`, `OAI.CubicTorus.isMinimizerAt_antitoneOn_axialSectionArea`, `OAI.CubicTorus.isMinimizerAt_axialFluxWeight_pos`, `OAI.CubicTorus.isMinimizerAt_axialHeight_absolutelyContinuous`, `OAI.CubicTorus.isMinimizerAt_axial_boundary_null`, `OAI.CubicTorus.isMinimizerAt_axial_endFlux`, `OAI.CubicTorus.isMinimizerAt_axial_endpoint_perimeter`, `OAI.CubicTorus.isMinimizerAt_bottom_both_extents`, `OAI.CubicTorus.isMinimizerAt_bottom_extent_calibration`, `OAI.CubicTorus.isMinimizerAt_boundary_slice_null_ae`, `OAI.CubicTorus.isMinimizerAt_centeredJacobiChart`, `OAI.CubicTorus.isMinimizerAt_centered_C1_modulus`, `OAI.CubicTorus.isMinimizerAt_centered_multiplier`, `OAI.CubicTorus.isMinimizerAt_chamber_continuous_exit`, `OAI.CubicTorus.isMinimizerAt_chamber_upper_downset`, `OAI.CubicTorus.isMinimizerAt_connected_curvature_integral_pos`, `OAI.CubicTorus.isMinimizerAt_connected_reflection_geometry`, `OAI.CubicTorus.isMinimizerAt_coordinate_cylinder_phase`, `OAI.CubicTorus.isMinimizerAt_cylinder_contact_standard`, `OAI.CubicTorus.isMinimizerAt_cylindrical_standard_tube`, `OAI.CubicTorus.isMinimizerAt_density_pos`, `OAI.CubicTorus.isMinimizerAt_first_transition_nonstandard_two_vertices`, `OAI.CubicTorus.isMinimizerAt_first_transition_standard`, `OAI.CubicTorus.isMinimizerAt_four_corner_necessary_data`, `OAI.CubicTorus.isMinimizerAt_global_normal`, `OAI.CubicTorus.isMinimizerAt_improved_section_weight_ae`, `OAI.CubicTorus.isMinimizerAt_lipschitz_approximation_with_cones`, `OAI.CubicTorus.isMinimizerAt_mean_square_equality_spherical`, `OAI.CubicTorus.isMinimizerAt_measurable_weighted_area_bound`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_flux_unrestricted`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_seam_bound`, `OAI.CubicTorus.isMinimizerAt_missing_neighbor_sharp_area_flux`, `OAI.CubicTorus.isMinimizerAt_nesting_cubic_gain`, `OAI.CubicTorus.isMinimizerAt_nesting_improved_profile_circle`, `OAI.CubicTorus.isMinimizerAt_no_monotone_revolution`, `OAI.CubicTorus.isMinimizerAt_nonstandard_integrated_flux`, `OAI.CubicTorus.isMinimizerAt_nonstandard_section_system`, `OAI.CubicTorus.isMinimizerAt_nonstandard_strict_octant`, `OAI.CubicTorus.isMinimizerAt_normalGraph_good_energy`, `OAI.CubicTorus.isMinimizerAt_normal_coordinate_strict_or_zero`, `OAI.CubicTorus.isMinimizerAt_one_vertex_standard_ball`, `OAI.CubicTorus.isMinimizerAt_periodic_ae_eq_boundary`, `OAI.CubicTorus.isMinimizerAt_positive_position_spherical`, `OAI.CubicTorus.isMinimizerAt_radial_slice_length_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_reflection_symmetry_of_competitor`, `OAI.CubicTorus.isMinimizerAt_reflection_weak_normal_sign`, `OAI.CubicTorus.isMinimizerAt_rotation_jacobi_from_germs`, `OAI.CubicTorus.isMinimizerAt_second_transition_nonstandard_star`, `OAI.CubicTorus.isMinimizerAt_section_extent_perimeter`, `OAI.CubicTorus.isMinimizerAt_section_improved_profile`, `OAI.CubicTorus.isMinimizerAt_section_planar_profile`, `OAI.CubicTorus.isMinimizerAt_section_strip_perimeter`, `OAI.CubicTorus.isMinimizerAt_sharp_section_weight_ae`, `OAI.CubicTorus.isMinimizerAt_slice_absolutelyContinuous`, `OAI.CubicTorus.isMinimizerAt_smaller_side_double_vertices_vacant`, `OAI.CubicTorus.isMinimizerAt_smooth_radial_section_of_level_vertices`, `OAI.CubicTorus.isMinimizerAt_spherical_standard_ball`, `OAI.CubicTorus.isMinimizerAt_three_vertex_bottom`, `OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation`, `OAI.CubicTorus.isMinimizerAt_tubular_sections`, `OAI.CubicTorus.isMinimizerAt_two_missing_vertices_top_flux`, `OAI.CubicTorus.isMinimizerAt_two_vertices_smooth_tube`, `OAI.CubicTorus.isMinimizerAt_zero_axis_cylindrical_boundary`, `OAI.CubicTorus.isMinimizerAt_zero_component_multiplier_ne_zero`, `OAI.CubicTorus.isMinimizerAt_zero_coordinate_cylindrical`, `OAI.CubicTorus.isMinimizerAt_zero_curvature_not_preconnected`, `OAI.CubicTorus.isoperimetricProfile_power_upper_support`, `OAI.CubicTorus.normalComponentScalar_global_jacobi`, `OAI.CubicTorus.normal_transverse_near_reflection_height` and `OAI.CubicTorus.strict_normal_component_ne_zero_ae` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVRadial.lean (declaration OAI.CubicTorus.isMinimizerAt_openRepresentative_ae)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

theorem isMinimizerAt_openRepresentative_ae {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    openRepresentative E =ᵐ[torusVolume] E := by
  sorry

end CubicTorus

end
end

end

end OAI
end
