-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_pow_s01
-- name    : OAI.MaximalSeshadri.Geometry.curveDegree_pow_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:54:27.881977+00:00
-- url     : https://prove2.me/theorems/49beab7f-5e89-4c6b-a4a1-e1087c2bd698
-- title:
--   OAI.MaximalSeshadri.Geometry.curveDegree_pow_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.curveDegree_pow` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/AmbientCurveDegree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/AmbientCurveDegree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem curveDegree_pow_s01 (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
--       (L : LineBundle S.scheme) (C : IntegralCurve S) (n : ℕ) :
--       curveDegree S (L.pow n) C = (n : ℤ) * curveDegree S L C
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.curveDegree` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive_s01`, `OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_arbitrary_jet_frames_s01`, `OAI.MaximalSeshadri.Geometry.Surface.eventually_effective_with_jets_s01`, `OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective_s01`, `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01`, `OAI.MaximalSeshadri.Geometry.generated_curveDegree_of_power_iso_s01`, `OAI.MaximalSeshadri.Geometry.generated_nodal_all_section_quadrilateral_s01`, `OAI.MaximalSeshadri.Geometry.generated_power_euler_difference_s01`, `OAI.MaximalSeshadri.Geometry.generated_twist_euler_difference_s01` and `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/AmbientCurveDegree.lean (declaration OAI.MaximalSeshadri.Geometry.curveDegree_pow)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES005

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

theorem curveDegree_pow_s01 (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) (C : IntegralCurve S) (n : ℕ) :
    curveDegree S (L.pow n) C = (n : ℤ) * curveDegree S L C := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
