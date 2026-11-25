-- Prove2me | Theorems.Thm_GlobalTheory_HL_GoodSub_count_eq
-- name    : GlobalTheory.HL.GoodSub.count_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:31:08.623833+00:00
-- url     : https://prove2.me/theorems/cfe3c05d-57b8-4c62-8337-1934e9a76ff9
-- title:
--   Good Sub: count eq
-- statement:
--   The Good Sub construction uses the count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommensurableCosetUnionContentIndependentNonneg.lean#L81-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommensurableCosetUnionContentIndependentNonneg.lean#L81-L91

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonneg
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
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.GoodSub.count_eq {W : Type} [AddCommGroup W] {W0 A B : AddSubgroup W} {S : Set W}
    (hA : GoodSub W0 A S) (hB : GoodSub W0 B S) :
    (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A =
      (((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard : ℝ) * relVol W0 B := by sorry
