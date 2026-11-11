-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IsBlowup_ample_exceptional_twist_s01
-- name    : OAI.MaximalSeshadri.Geometry.IsBlowup.ample_exceptional_twist_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:00:44.6366+00:00
-- url     : https://prove2.me/theorems/1daa5589-0469-497c-9482-e9005cd80e37
-- title:
--   OAI.MaximalSeshadri.Geometry.IsBlowup.ample_exceptional_twist_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.IsBlowup.ample_exceptional_twist` of [lean/OAI/AlgebraicGeometry/Seshadri/Geometry/RelativeProjectivity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/RelativeProjectivity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace`, `open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens MaximalSeshadri.Projective`):
--
--   ```lean
--   theorem IsBlowup.ample_exceptional_twist_s01 [IsIntegral B] [CompactSpace B]
--       [CompactSpace X] (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
--       (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
--       ∃ a n : ℕ, 0 < a ∧ 0 < n ∧
--         ((((L.pow a).pullback π).pow n).tensor J).IsAmple
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Frames.O` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pullback` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.pow` (definitions bundle `Q223SES005` of this split); `OAI.MaximalSeshadri.Geometry.LineBundle.tensor` (definitions bundle `Q223SES007` of this split); `OAI.MaximalSeshadri.Geometry.IsBlowup`, `OAI.MaximalSeshadri.Geometry.LineBundle`, `OAI.MaximalSeshadri.Geometry.PresentsPullbackIdeal` and `OAI.MaximalSeshadri.Geometry.LineBundle.IsAmple` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.pointBlowup_exists_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/RelativeProjectivity.lean (declaration OAI.MaximalSeshadri.Geometry.IsBlowup.ample_exceptional_twist)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES007

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instIsOpenImmersionComplementLift _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.SectionOpens MaximalSeshadri.Projective

variable {X : Scheme.{0}}

variable {B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.ample_exceptional_twist_s01 [IsIntegral B] [CompactSpace B]
    [CompactSpace X] (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ a n : ℕ, 0 < a ∧ 0 < n ∧
      ((((L.pow a).pullback π).pow n).tensor J).IsAmple := by
  sorry

end
end MaximalSeshadri.Geometry

end

end OAI
end
