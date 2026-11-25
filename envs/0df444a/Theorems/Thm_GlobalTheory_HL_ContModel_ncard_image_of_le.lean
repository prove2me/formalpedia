-- Prove2me | Theorems.Thm_GlobalTheory_HL_ContModel_ncard_image_of_le
-- name    : GlobalTheory.HL.ContModel.ncard_image_of_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:03.096606+00:00
-- url     : https://prove2.me/theorems/1b13c0c3-0973-507e-8cbc-f44b29ee976a
-- title:
--   Cont Model: ncard image of le
-- statement:
--   The Cont Model construction uses the ncard image of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L12-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/NcardImageOfLe.lean#L12-L37

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

theorem GlobalTheory.HL.ContModel.ncard_image_of_le {W : Type} [AddCommGroup W] {A B : AddSubgroup W} (h : B ≤ A) (S : Set W)
    (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard
      = ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * B.relIndex A := by sorry
