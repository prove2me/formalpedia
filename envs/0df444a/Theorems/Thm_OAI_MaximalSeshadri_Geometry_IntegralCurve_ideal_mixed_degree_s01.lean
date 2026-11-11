-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ideal_mixed_degree_s01
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:01:06.765068+00:00
-- url     : https://prove2.me/theorems/caf8fd4f-768b-447d-8ecd-665a3088fcc3
-- title:
--   OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/CurveIdealDegree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/CurveIdealDegree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem IntegralCurve.ideal_mixed_degree_s01 (S : Surface)
--       (A : LineBundle S.scheme) (hA : A.IsAmple) (C : IntegralCurve S)
--       (J : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
--       (h : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
--       (M : LineBundle S.scheme) :
--       mixedEuler S M J = -curveDegree S M C
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.mixedEuler` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.PresentsPullbackIdeal`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.curveDegree` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01`, `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01`, `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` and `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/CurveIdealDegree.lean (declaration OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

theorem IntegralCurve.ideal_mixed_degree_s01 (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (C : IntegralCurve S)
    (J : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (h : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (M : LineBundle S.scheme) :
    mixedEuler S M J = -curveDegree S M C := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
