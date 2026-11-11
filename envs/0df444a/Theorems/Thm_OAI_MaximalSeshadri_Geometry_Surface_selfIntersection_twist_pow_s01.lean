-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_selfIntersection_twist_pow_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:05:33.744808+00:00
-- url     : https://prove2.me/theorems/0cc08bcf-0840-4580-b6ae-42db4fd784a0
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/BivariateSurfaceEuler.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/BivariateSurfaceEuler.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem Surface.selfIntersection_twist_pow_s01 (S : Surface)
--       (L : LineBundle S.scheme) (hL : L.IsAmple) (J : LineBundle S.scheme) (a b : ℕ) :
--       selfIntersection S ((L.pow a).tensor (J.pow b)) =
--         (a : ℤ)^2*selfIntersection S L + 2*(a : ℤ)*(b : ℤ)*mixedEuler S L J +
--           (b : ℤ)^2*selfIntersection S J
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.mixedEuler` and `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.selfIntersection` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/BivariateSurfaceEuler.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow)

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
open MaximalSeshadri.Frames

theorem Surface.selfIntersection_twist_pow_s01 (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (J : LineBundle S.scheme) (a b : ℕ) :
    selfIntersection S ((L.pow a).tensor (J.pow b)) =
      (a : ℤ)^2*selfIntersection S L + 2*(a : ℤ)*(b : ℤ)*mixedEuler S L J +
        (b : ℤ)^2*selfIntersection S J := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
