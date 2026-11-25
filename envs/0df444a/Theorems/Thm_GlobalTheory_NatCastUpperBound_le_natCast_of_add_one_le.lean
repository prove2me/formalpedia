-- Prove2me | Theorems.Thm_GlobalTheory_NatCastUpperBound_le_natCast_of_add_one_le
-- name    : GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:53.290107+00:00
-- url     : https://prove2.me/theorems/e963ffd9-5205-48d4-9e04-bc6bab17f99a
-- title:
--   Nat Cast Upper Bound: le nat Cast of add one le
-- statement:
--   The Nat Cast Upper Bound construction uses the le nat Cast of add one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeNatCastOfAddOneLe.lean#L5-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeNatCastOfAddOneLe.lean#L5-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeNatCastOfAddOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatCastUpperBound

theorem GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le {a : WithBot ℕ∞} {n : ℕ}
    (h : a + (1 : WithBot ℕ∞) ≤ (↑(n + (1 : ℕ)) : WithBot ℕ∞)) :
    a ≤ (↑n : WithBot ℕ∞) := by sorry
