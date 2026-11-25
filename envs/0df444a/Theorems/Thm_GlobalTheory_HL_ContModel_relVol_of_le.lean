-- Prove2me | Theorems.Thm_GlobalTheory_HL_ContModel_relVol_of_le
-- name    : GlobalTheory.HL.ContModel.relVol_of_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:14:35.316394+00:00
-- url     : https://prove2.me/theorems/f7588fc9-0012-410c-bf83-383f76aa9d92
-- title:
--   Cont Model: rel Vol of le
-- statement:
--   The Cont Model construction uses the rel Vol of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L41-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L41-L58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
open ValuativeRel
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.ContModel.relVol_of_le {W : Type} [AddCommGroup W]
    {W0 A B : AddSubgroup W} (h : B ≤ A) (hB : B.relIndex W0 ≠ 0) :
    _root_.GlobalTheory.HL.relVol W0 A = B.relIndex A * _root_.GlobalTheory.HL.relVol W0 B := by sorry
