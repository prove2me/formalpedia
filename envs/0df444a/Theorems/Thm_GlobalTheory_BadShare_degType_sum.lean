-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_degType_sum
-- name    : GlobalTheory.BadShare.degType_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:58:56.295907+00:00
-- url     : https://prove2.me/theorems/50fe1686-0aae-4a09-aa2a-5fb1726c4c76
-- title:
--   Bad Share: deg Type sum
-- statement:
--   The Bad Share construction uses the deg Type sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusCardBoundsAndMul.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusCardBoundsAndMul.lean#L12-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusCardBoundsAndMul
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

theorem GlobalTheory.BadShare.degType_sum (g : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) (hf : f ≠ 0) :
    (degType g f).sum = f.natDegree := by sorry
