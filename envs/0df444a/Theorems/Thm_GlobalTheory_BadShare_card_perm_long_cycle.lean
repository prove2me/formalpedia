-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_card_perm_long_cycle
-- name    : GlobalTheory.BadShare.card_perm_long_cycle
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:58:51.15265+00:00
-- url     : https://prove2.me/theorems/287e2bd1-c9f2-45f5-a27c-7b8ebf2696ab
-- title:
--   Bad Share: card perm long cycle
-- statement:
--   The Bad Share construction uses the card perm long cycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardCycleTypeConsMul.lean#L88-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardCycleTypeConsMul.lean#L88-L116

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

theorem GlobalTheory.BadShare.card_perm_long_cycle : ∀ N p : ℕ, N < 2 * p → p ≤ N →
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card * p
      = N.factorial := by sorry
