-- Prove2me | Theorems.Thm_GlobalTheory_StandardAdditiveCharacter_exists_stdAddChar_eq
-- name    : GlobalTheory.StandardAdditiveCharacter.exists_stdAddChar_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:22:13.776511+00:00
-- url     : https://prove2.me/theorems/dd8472ec-d23f-466a-a0e0-4fc27536351c
-- title:
--   Standard Additive Character: exists std Add Char eq
-- statement:
--   The Standard Additive Character construction uses the exists std Add Char eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveDualAddChar.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveDualAddChar.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveDualAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.StandardAdditiveCharacter

theorem GlobalTheory.StandardAdditiveCharacter.exists_stdAddChar_eq (n : ℕ) [NeZero n] (z : ℂ) (hz : z ^ n = 1) :
    ∃ j : ZMod n, ZMod.stdAddChar j = z := by sorry
