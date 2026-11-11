-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_mixedEuler_pow_right_s01
-- name    : OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:01:51.820471+00:00
-- url     : https://prove2.me/theorems/cb3d3655-7558-44b6-893a-f92bc72c2c75
-- title:
--   OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/MixedIntersection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/MixedIntersection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem mixedEuler_pow_right_s01 (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
--       (M : LineBundle S.scheme) (n : ℕ) :
--       mixedEuler S L (M.pow n) = (n : ℤ)*mixedEuler S L M
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.mixedEuler` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.PointBlowup.effective_twist_bound_s01`, `OAI.MaximalSeshadri.Geometry.Surface.blowup_intersections_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01`, `OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective_s01`, `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_general_s01`, `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow_s01`, `OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01`, `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01` and `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_general_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/MixedIntersection.lean (declaration OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem mixedEuler_pow_right_s01 (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) (n : ℕ) :
    mixedEuler S L (M.pow n) = (n : ℤ)*mixedEuler S L M := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
