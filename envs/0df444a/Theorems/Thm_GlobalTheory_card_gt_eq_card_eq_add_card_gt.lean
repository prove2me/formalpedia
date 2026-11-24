-- Prove2me | Theorems.Thm_GlobalTheory_card_gt_eq_card_eq_add_card_gt
-- name    : GlobalTheory.card_gt_eq_card_eq_add_card_gt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:04.148802+00:00
-- url     : https://prove2.me/theorems/10ffd5ac-6fbe-42dd-9c04-17a3db40ace8
-- title:
--   Global Theory: card gt eq card eq add card gt
-- statement:
--   The Global Theory construction uses the card gt eq card eq add card gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsPermOfSumMinEqPositiveFamily.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsPermOfSumMinEqPositiveFamily.lean#L13-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory

theorem GlobalTheory.card_gt_eq_card_eq_add_card_gt {d : ℕ} (e : Fin d → ℕ) (j : ℕ) :
    (Finset.univ.filter (fun i => j < e i)).card =
      (Finset.univ.filter (fun i => e i = j + 1)).card +
        (Finset.univ.filter (fun i => j + 1 < e i)).card := by sorry
