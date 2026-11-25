-- Prove2me | Theorems.Thm_GlobalTheory_NatCastStrictBound_lt_natCast_of_add_one_lt_succ
-- name    : GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:52.069327+00:00
-- url     : https://prove2.me/theorems/8fb4ac67-6ca5-4fc1-bb32-ae3a20ab02fa
-- title:
--   Nat Cast Strict Bound: lt nat Cast of add one lt succ
-- statement:
--   The Nat Cast Strict Bound construction uses the lt nat Cast of add one lt succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LtNatCastOfAddOneLtSucc.lean#L5-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LtNatCastOfAddOneLtSucc.lean#L5-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LtNatCastOfAddOneLtSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatCastStrictBound

theorem GlobalTheory.NatCastStrictBound.lt_natCast_of_add_one_lt_succ :
    ∀ {a : WithBot ℕ∞} {n : ℕ}, a + (1 : WithBot ℕ∞) < (↑(n + (1 : ℕ)) : WithBot ℕ∞) →
      a < (↑n : WithBot ℕ∞) := by sorry
