-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:07:00.821969+00:00
-- url     : https://prove2.me/theorems/e2d6a014-f238-4d02-8a84-4d349a4326b7
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section` of [lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CoprimeDivisor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CoprimeDivisor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral`):
--
--   ```lean
--   theorem Surface.coprime_integral_section_s01 (S : Surface) (L : LineBundle S.scheme)
--       (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
--       ∃ b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ ∃ N : ℕ,
--         ∃ s : Option (Fin N) → GlobalSections S.scheme (L.pow b).sheaf,
--         ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
--         ∃ v : Option (Fin N) → ℂ,
--           let k := S.structureMap.appTop.hom.comp
--             (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
--           sectionCombination k s v ≠ 0 ∧ IsIntegral (sectionIdeal k s hs v).subscheme ∧
--             topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.SectionOpens.isoOpen` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Projective.sectionCombination` (definitions bundle `Q223SES006` of this split); `OAI.MaximalSeshadri.Projective.sectionIdeal` (definitions bundle `Q223SES009` of this split); `OAI.MaximalSeshadri.Geometry.GlobalSections`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.structureSheaf` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.blowup_intersections_s01`, `OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventual_etale_affine_section_test_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01`, `OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective_s01`, `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01`, `OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded_s01`, `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_general_s01`, `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow_s01`, `OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01`, `OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections_s01`, `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_eq_mixedEuler_s01`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01`, `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01`, `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_general_s01`, `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_s01`, `OAI.MaximalSeshadri.Geometry.mixedEuler_tensor_right_general_s01` and `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CoprimeDivisor.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.coprime_integral_section_s01 (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (L.pow b).sheaf,
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ v : Option (Fin N) → ℂ,
        let k := S.structureMap.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        sectionCombination k s v ≠ 0 ∧ IsIntegral (sectionIdeal k s hs v).subscheme ∧
          topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1 := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
