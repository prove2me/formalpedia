-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_square_squeeze_of_sections_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:55:21.65776+00:00
-- url     : https://prove2.me/theorems/c59be822-075b-48d8-a62d-03a26d65a0f7
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections` of [lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersectionGrowth.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersectionGrowth.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   lemma Surface.square_squeeze_of_sections_s01 (S T : Surface)
--       (L : LineBundle S.scheme) (hL : L.IsAmple)
--       (D : LineBundle T.scheme) (hD : D.IsAmple) (k r : ℕ)
--       (hb : ∀ n : ℕ,
--         cohomologyDimension T.structureMap (D.pow n).sheaf 0 ≤ cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ∧
--         2*cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ≤
--           2*cohomologyDimension T.structureMap (D.pow n).sheaf 0 + r*n*(n+1)) :
--       (k:ℤ)^2*selfIntersection S L-r ≤ selfIntersection T D ∧
--       selfIntersection T D ≤ (k:ℤ)^2*selfIntersection S L
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.cohomologyDimension`, `OAI.MaximalSeshadri.Geometry.selfIntersection` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.ample_exceptional_square_squeeze_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersectionGrowth.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES005

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
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

lemma Surface.square_squeeze_of_sections_s01 (S T : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple)
    (D : LineBundle T.scheme) (hD : D.IsAmple) (k r : ℕ)
    (hb : ∀ n : ℕ,
      cohomologyDimension T.structureMap (D.pow n).sheaf 0 ≤ cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ∧
      2*cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ≤
        2*cohomologyDimension T.structureMap (D.pow n).sheaf 0 + r*n*(n+1)) :
    (k:ℤ)^2*selfIntersection S L-r ≤ selfIntersection T D ∧
    selfIntersection T D ≤ (k:ℤ)^2*selfIntersection S L := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
