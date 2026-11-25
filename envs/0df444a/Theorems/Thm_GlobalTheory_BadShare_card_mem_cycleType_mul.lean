-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_card_mem_cycleType_mul
-- name    : GlobalTheory.BadShare.card_mem_cycleType_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:39.236388+00:00
-- url     : https://prove2.me/theorems/a312d8e1-d992-497e-b9af-7083a7111614
-- title:
--   Bad Share: card mem cycle Type mul
-- statement:
--   The Bad Share construction uses the card mem cycle Type mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardCycleTypeConsMul.lean#L37-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardCycleTypeConsMul.lean#L37-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardCycleTypeConsMul
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
open Equiv Finset

theorem GlobalTheory.BadShare.card_mem_cycleType_mul (N p : ℕ) (hp : 2 ≤ p) (hN : N < 2 * p) (hpN : p ≤ N) :
    (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p = N.factorial := by sorry
