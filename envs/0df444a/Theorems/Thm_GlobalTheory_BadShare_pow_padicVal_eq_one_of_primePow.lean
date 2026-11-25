-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_pow_padicVal_eq_one_of_primePow
-- name    : GlobalTheory.BadShare.pow_padicVal_eq_one_of_primePow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:05.166147+00:00
-- url     : https://prove2.me/theorems/81bb1e34-d0cd-4d8f-9fb9-54e3f7398524
-- title:
--   Bad Share: pow padic Val eq one of prime Pow
-- statement:
--   The Bad Share construction uses the pow padic Val eq one of prime Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PowPadicValEqOneOfPrimePow.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PowPadicValEqOneOfPrimePow.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PowPadicValEqOneOfPrimePow
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

theorem GlobalTheory.BadShare.pow_padicVal_eq_one_of_primePow {k : Type} [Field k] {n l : ℕ} (hn : 0 < n) (hl : l.Prime) {y : k}
    (h1 : y ^ n = 1) {a : ℕ} (h2 : y ^ (l ^ a) = 1) : y ^ (l ^ padicValNat l n) = 1 := by sorry
