-- Prove2me | Theorems.Thm_GlobalTheory_HL_ContAut_relVol_mul
-- name    : GlobalTheory.HL.ContAut.relVol_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:15.175015+00:00
-- url     : https://prove2.me/theorems/350b622d-cb45-4061-8495-3fd3b7f61003
-- title:
--   Cont Aut: rel Vol mul
-- statement:
--   The Cont Aut construction uses the rel Vol mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelVolMul.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelVolMul.lean#L12-L26

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContAut

theorem GlobalTheory.HL.ContAut.relVol_mul {W : Type} [AddCommGroup W] {X Y B : AddSubgroup W}
    (hYX : Y.relIndex X ≠ 0) (hBY : B.relIndex Y ≠ 0) :
    relVol X B = relVol X Y * relVol Y B := by sorry
