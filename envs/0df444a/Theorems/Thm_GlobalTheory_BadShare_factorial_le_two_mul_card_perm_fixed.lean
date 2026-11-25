-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_factorial_le_two_mul_card_perm_fixed
-- name    : GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:58:49.622204+00:00
-- url     : https://prove2.me/theorems/1f5f59af-b01f-4c25-a9da-e1df0a3e37c9
-- title:
--   Bad Share: factorial le two mul card perm fixed
-- statement:
--   The Bad Share construction uses the factorial le two mul card perm fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FactorialLeTwoMulCardPermWithFixedPoint.lean#L24-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FactorialLeTwoMulCardPermWithFixedPoint.lean#L24-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare

theorem GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed :
    ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α →
      (Fintype.card α).factorial ≤
        2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by sorry
