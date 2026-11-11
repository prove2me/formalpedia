-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_power_H0_quadratic_upper_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:55:21.353978+00:00
-- url     : https://prove2.me/theorems/f5b045a3-2b57-46f7-bf32-74e1c2a47d6a
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper` of [lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH1Growth.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH1Growth.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem Surface.power_H0_quadratic_upper_s01 (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
--       ∃ B G : ℕ, ∀ n : ℕ,
--         2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) ≤
--         (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
--         2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
--           eulerCharacteristic S.structureMap 2 (O S.scheme)) +
--         2*eulerCharacteristic S.structureMap 2 (O S.scheme) + 2*B+2*G*n
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.cohomologyDimension`, `OAI.MaximalSeshadri.Geometry.eulerCharacteristic`, `OAI.MaximalSeshadri.Geometry.selfIntersection` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH1Growth.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.power_H0_quadratic_upper)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES005

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

theorem Surface.power_H0_quadratic_upper_s01 (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B G : ℕ, ∀ n : ℕ,
      2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) ≤
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) + 2*B+2*G*n := by
  sorry
end
end MaximalSeshadri.Geometry

end

end OAI
end
