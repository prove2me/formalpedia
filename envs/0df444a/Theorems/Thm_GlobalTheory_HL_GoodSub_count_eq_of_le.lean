-- Prove2me | Theorems.Thm_GlobalTheory_HL_GoodSub_count_eq_of_le
-- name    : GlobalTheory.HL.GoodSub.count_eq_of_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:31:02.18462+00:00
-- url     : https://prove2.me/theorems/19f7fa3b-f271-4872-a133-c0c0c65a3f78
-- title:
--   Good Sub: count eq of le
-- statement:
--   The Good Sub construction uses the count eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommensurableCosetUnionContentIndependentNonneg.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommensurableCosetUnionContentIndependentNonneg.lean#L73-L79

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

theorem GlobalTheory.HL.GoodSub.count_eq_of_le {W : Type} [AddCommGroup W] {W0 A A' : AddSubgroup W} {S : Set W}
    (h : GoodSub W0 A S) (hle : A' ≤ A) (hi : A'.relIndex A ≠ 0) :
    (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A =
      (((QuotientAddGroup.mk : W → W ⧸ A') '' S).ncard : ℝ) * relVol W0 A' := by sorry
