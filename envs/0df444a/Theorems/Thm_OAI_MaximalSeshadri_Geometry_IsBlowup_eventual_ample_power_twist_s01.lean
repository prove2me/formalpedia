-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IsBlowup_eventual_ample_power_twist_s01
-- name    : OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:02:13.085237+00:00
-- url     : https://prove2.me/theorems/e0cbbb45-6e23-4fa0-b5f9-05c9336dd958
-- title:
--   OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist` of [lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory TopologicalSpace`, `open MaximalSeshadri.Frames`):
--
--   ```lean
--   lemma IsBlowup.eventual_ample_power_twist_s01 {X Y : Scheme.{0}} [IsIntegral Y]
--       [CompactSpace Y] [CompactSpace X] {I : X.IdealSheafData} {f : Y ⟶ X}
--       (hb : IsBlowup I f) (L : LineBundle X) (hL : L.IsAmple)
--       (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι) :
--       ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
--         (((L.pullback f).pow (a*(n+1))).tensor J).IsAmple
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pullback` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.IsBlowup`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.PresentsPullbackIdeal` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proofs of `OAI.MaximalSeshadri.Geometry.Surface.blowup_intersections_s01` and `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` of this split import it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersection.lean (declaration OAI.MaximalSeshadri.Geometry.IsBlowup.eventual_ample_power_twist)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
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

lemma IsBlowup.eventual_ample_power_twist_s01 {X Y : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [CompactSpace X] {I : X.IdealSheafData} {f : Y ⟶ X}
    (hb : IsBlowup I f) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι) :
    ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
      (((L.pullback f).pow (a*(n+1))).tensor J).IsAmple := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
