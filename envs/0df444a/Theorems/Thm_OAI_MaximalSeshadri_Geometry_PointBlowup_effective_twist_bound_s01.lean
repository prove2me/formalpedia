-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_PointBlowup_effective_twist_bound_s01
-- name    : OAI.MaximalSeshadri.Geometry.PointBlowup.effective_twist_bound_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:00:29.125757+00:00
-- url     : https://prove2.me/theorems/5a6a68ec-a935-4bb4-ac75-ae2b78229d4a
-- title:
--   OAI.MaximalSeshadri.Geometry.PointBlowup.effective_twist_bound_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.PointBlowup.effective_twist_bound` of [lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupEffectiveBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupEffectiveBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   theorem PointBlowup.effective_twist_bound_s01 (S : Surface) (L : LineBundle S.scheme)
--       (hL : L.IsAmple) {r : ℕ} {p : Configuration S r} (B : PointBlowup S r p)
--       (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
--       (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
--       (w : ℝ) (hw : 0 ≤ w)
--       (hC : ∀ C : IntegralCurve S,
--         w*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
--       (I : LineBundle B.surface.scheme) (τ : I.sheaf ⟶ O B.surface.scheme) [Mono τ]
--       (k m b n : ℕ) (hn : 0 < n)
--       (s : O B.surface.scheme ⟶
--         ((((((L.pullback B.projection).pow k).tensor (J.pow m)).pow 1).tensor (I.pow b)).pow n).sheaf)
--       (hs : s ≠ 0) : w*((r*m:ℕ):ℝ) ≤ (k:ℝ)*selfIntersection S L
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pullback` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.Configuration`, `OAI.MaximalSeshadri.Geometry.IntegralCurve`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.PointBlowup`, `OAI.MaximalSeshadri.Geometry.PresentsPullbackIdeal`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.centreIdeal`, `OAI.MaximalSeshadri.Geometry.curveDegree`, `OAI.MaximalSeshadri.Geometry.selfIntersection`, `OAI.MaximalSeshadri.Geometry.totalMultiplicity` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupEffectiveBound.lean (declaration OAI.MaximalSeshadri.Geometry.PointBlowup.effective_twist_bound)

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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

theorem PointBlowup.effective_twist_bound_s01 (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} {p : Configuration S r} (B : PointBlowup S r p)
    (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
    (w : ℝ) (hw : 0 ≤ w)
    (hC : ∀ C : IntegralCurve S,
      w*(totalMultiplicity S r C p:ℝ) ≤ (curveDegree S L C:ℝ))
    (I : LineBundle B.surface.scheme) (τ : I.sheaf ⟶ O B.surface.scheme) [Mono τ]
    (k m b n : ℕ) (hn : 0 < n)
    (s : O B.surface.scheme ⟶
      ((((((L.pullback B.projection).pow k).tensor (J.pow m)).pow 1).tensor (I.pow b)).pow n).sheaf)
    (hs : s ≠ 0) : w*((r*m:ℕ):ℝ) ≤ (k:ℝ)*selfIntersection S L := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
