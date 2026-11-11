-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_selfIntersection_twist_general_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_general_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:01:03.363774+00:00
-- url     : https://prove2.me/theorems/cd512268-485c-46c1-8143-d5c32ff9a694
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_general_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_general` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/IntersectionBilinear.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/IntersectionBilinear.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   lemma Surface.selfIntersection_twist_general_s01 (S : Surface) (A : LineBundle S.scheme)
--       (hA : A.IsAmple) (M N : LineBundle S.scheme) (a b : ℕ) :
--       selfIntersection S ((M.pow a).tensor (N.pow b)) =
--         (a : ℤ)^2*selfIntersection S M + 2*(a : ℤ)*(b : ℤ)*mixedEuler S M N +
--           (b : ℤ)^2*selfIntersection S N
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.mixedEuler` and `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.selfIntersection` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/IntersectionBilinear.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_general)

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

lemma Surface.selfIntersection_twist_general_s01 (S : Surface) (A : LineBundle S.scheme)
    (hA : A.IsAmple) (M N : LineBundle S.scheme) (a b : ℕ) :
    selfIntersection S ((M.pow a).tensor (N.pow b)) =
      (a : ℤ)^2*selfIntersection S M + 2*(a : ℤ)*(b : ℤ)*mixedEuler S M N +
        (b : ℤ)^2*selfIntersection S N := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
