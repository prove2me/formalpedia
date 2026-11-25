-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_SqCount_card_not_squarefree
-- name    : GlobalTheory.BadShare.SqCount.card_not_squarefree
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:56:53.346893+00:00
-- url     : https://prove2.me/theorems/8427ff0e-ee02-4e66-a349-ff09d3298608
-- title:
--   Sq Count: card not squarefree
-- statement:
--   The Sq Count construction uses the card not squarefree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardMonicSquarefreeUnitConstPolysGe.lean#L98-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardMonicSquarefreeUnitConstPolysGe.lean#L98-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.SqCount
variable (g : ℕ) [Fact g.Prime]
variable {g}

theorem GlobalTheory.BadShare.SqCount.card_not_squarefree (n : ℕ) : ((monicSet g (n + 1)).filter fun f => ¬ Squarefree f).card ≤ g ^ n := by sorry
