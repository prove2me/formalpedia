-- Prove2me | Theorems.Thm_GlobalTheory_T_card_monicSquarefreeUnitConstPolys_ge
-- name    : GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:59:50.474114+00:00
-- url     : https://prove2.me/theorems/f81c25c5-beb5-529c-81cd-89b978abe029
-- title:
--   T: card monic Squarefree Unit Const Polys ge
-- statement:
--   The T construction uses the card monic Squarefree Unit Const Polys ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardMonicSquarefreeUnitConstPolysGeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardMonicSquarefreeUnitConstPolysGeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGeStatement
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

theorem GlobalTheory.T.card_monicSquarefreeUnitConstPolys_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 1 ≤ N → (g : ℝ) ^ N - 2 * (g : ℝ) ^ (N - 1) ≤ ((sqSet g N).card : ℝ) := by sorry
