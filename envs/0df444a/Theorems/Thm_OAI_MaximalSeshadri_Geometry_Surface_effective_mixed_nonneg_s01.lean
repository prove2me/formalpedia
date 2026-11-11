-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_effective_mixed_nonneg_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:00:18.205613+00:00
-- url     : https://prove2.me/theorems/02521f86-9cef-41dc-a995-b0abd06f71f9
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg` of [lean/OAI/AlgebraicGeometry/Seshadri/Intersection/EffectiveDegree.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/EffectiveDegree.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini`):
--
--   ```lean
--   theorem Surface.effective_mixed_nonneg_s01 (S : Surface) (L : LineBundle S.scheme)
--       (hL : L.IsAmple) (M : LineBundle S.scheme)
--       (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0) : 0 ≤ mixedEuler S L M
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.mixedEuler` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.section_bound_of_curve_bound_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/EffectiveDegree.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg)

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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

theorem Surface.effective_mixed_nonneg_s01 (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (M : LineBundle S.scheme)
    (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0) : 0 ≤ mixedEuler S L M := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
