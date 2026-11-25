-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_two_mul_numDerangements_succ_le
-- name    : GlobalTheory.BadShare.two_mul_numDerangements_succ_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:40.060715+00:00
-- url     : https://prove2.me/theorems/c0e0b8b3-1d92-444f-ba84-05558cbc0188
-- title:
--   Bad Share: two mul num Derangements succ le
-- statement:
--   The Bad Share construction uses the two mul num Derangements succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FactorialLeTwoMulCardPermWithFixedPoint.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FactorialLeTwoMulCardPermWithFixedPoint.lean#L7-L22

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

theorem GlobalTheory.BadShare.two_mul_numDerangements_succ_le (n : ℕ) :
    2 * numDerangements (n + 1) ≤ (n + 1).factorial := by sorry
