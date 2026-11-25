-- Prove2me | Theorems.Thm_GlobalTheory_HL_ncard_image_mk_of_le
-- name    : GlobalTheory.HL.ncard_image_mk_of_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:37:25.918902+00:00
-- url     : https://prove2.me/theorems/ba4ebf11-f7e7-534c-a6a5-1f3b0716a515
-- title:
--   HL: ncard image mk of le
-- statement:
--   The HL construction uses the ncard image mk of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommensurableCosetUnionContentIndependentNonneg.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CommensurableCosetUnionContentIndependentNonneg.lean#L31-L38

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

theorem GlobalTheory.HL.ncard_image_mk_of_le {W : Type} [AddCommGroup W] {A A' : AddSubgroup W} {S : Set W}
    (hle : A' ≤ A) (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ A') '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * A'.relIndex A := by sorry
