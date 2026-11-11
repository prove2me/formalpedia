-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_ample_exceptional_square_squeeze_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.ample_exceptional_square_squeeze_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:59:35.346205+00:00
-- url     : https://prove2.me/theorems/d33741c0-bef7-4254-850c-ea1d1ebb8672
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.ample_exceptional_square_squeeze_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.ample_exceptional_square_squeeze` of [lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersectionGrowth.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersectionGrowth.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem Surface.ample_exceptional_square_squeeze_s01 (S T : Surface)
--       (L : LineBundle S.scheme) (hL : L.IsAmple)
--       {r : ℕ} (p : Configuration S r) (f : T.scheme ⟶ S.scheme)
--       (hf : f ≫ S.structureMap = T.structureMap)
--       (hbl : IsBlowup (centreIdeal S r p) f)
--       (J : LineBundle T.scheme) (ι : J.sheaf ⟶ O T.scheme)
--       (hJ : PresentsPullbackIdeal (centreIdeal S r p) f J ι)
--       (k : ℕ) (hD : (((L.pullback f).pow k).tensor J).IsAmple) :
--       (k:ℤ)^2*selfIntersection S L-r ≤ selfIntersection T (((L.pullback f).pow k).tensor J) ∧
--       selfIntersection T (((L.pullback f).pow k).tensor J) ≤ (k:ℤ)^2*selfIntersection S L
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pullback` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.Configuration`, `OAI.MaximalSeshadri.Geometry.IsBlowup`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.PresentsPullbackIdeal`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.centreIdeal`, `OAI.MaximalSeshadri.Geometry.selfIntersection` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.blowup_intersections_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersectionGrowth.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.ample_exceptional_square_squeeze)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

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

theorem Surface.ample_exceptional_square_squeeze_s01 (S T : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple)
    {r : ℕ} (p : Configuration S r) (f : T.scheme ⟶ S.scheme)
    (hf : f ≫ S.structureMap = T.structureMap)
    (hbl : IsBlowup (centreIdeal S r p) f)
    (J : LineBundle T.scheme) (ι : J.sheaf ⟶ O T.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) f J ι)
    (k : ℕ) (hD : (((L.pullback f).pow k).tensor J).IsAmple) :
    (k:ℤ)^2*selfIntersection S L-r ≤ selfIntersection T (((L.pullback f).pow k).tensor J) ∧
    selfIntersection T (((L.pullback f).pow k).tensor J) ≤ (k:ℤ)^2*selfIntersection S L := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
