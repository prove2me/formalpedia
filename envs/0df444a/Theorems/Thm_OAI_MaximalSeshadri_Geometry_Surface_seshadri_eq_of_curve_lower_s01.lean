-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_seshadri_eq_of_curve_lower_s01
-- name    : OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:45:08.990685+00:00
-- url     : https://prove2.me/theorems/b2a4a403-ce5c-4944-8ad6-bb983f332528
-- title:
--   OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower` of [lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/SeshadriUpper.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/SeshadriUpper.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`):
--
--   ```lean
--   lemma Surface.seshadri_eq_of_curve_lower_s01 (S : Surface) (L : LineBundle S.scheme)
--       (hL : L.IsAmple) {r : ℕ} (hr : 0 < r) (p : Configuration S r)
--       (hC : ∀ C : IntegralCurve S,
--         Real.sqrt ((selfIntersection S L:ℝ)/r)*(totalMultiplicity S r C p:ℝ) ≤
--           (curveDegree S L C:ℝ)) :
--       seshadriConstant S L r p = Real.sqrt ((selfIntersection S L:ℝ)/r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.Configuration`, `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.curveDegree`, `OAI.MaximalSeshadri.Geometry.selfIntersection`, `OAI.MaximalSeshadri.Geometry.seshadriConstant`, `OAI.MaximalSeshadri.Geometry.totalMultiplicity` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Interpolation/SeshadriUpper.lean (declaration OAI.MaximalSeshadri.Geometry.Surface.seshadri_eq_of_curve_lower)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma Surface.seshadri_eq_of_curve_lower_s01 (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (hr : 0 < r) (p : Configuration S r)
    (hC : ∀ C : IntegralCurve S,
      Real.sqrt ((selfIntersection S L:ℝ)/r)*(totalMultiplicity S r C p:ℝ) ≤
        (curveDegree S L C:ℝ)) :
    seshadriConstant S L r p = Real.sqrt ((selfIntersection S L:ℝ)/r) := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
