-- Prove2me | Theorems.Thm_GlobalTheory_T_factorial_le_two_mul_card_perm_with_fixedPoint
-- name    : GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:52:48.240195+00:00
-- url     : https://prove2.me/theorems/bb305194-d17c-455f-b89d-69136359265b
-- title:
--   T: factorial le two mul card perm with fixed Point
-- statement:
--   The T construction uses the factorial le two mul card perm with fixed Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FactorialLeTwoMulCardPermWithFixedPointStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FactorialLeTwoMulCardPermWithFixedPointStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPoint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint : ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α → (Fintype.card α).factorial ≤ 2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by sorry
