-- Prove2me | Theorems.Thm_GlobalTheory_sum_min_succ_eq_add_card
-- name    : GlobalTheory.sum_min_succ_eq_add_card
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:07.687216+00:00
-- url     : https://prove2.me/theorems/a812cb39-7a8b-4823-87ab-0588383dc42d
-- title:
--   Global Theory: sum min succ eq add card
-- statement:
--   The Global Theory construction uses the sum min succ eq add card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsPermOfSumMinEqPositiveFamily.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsPermOfSumMinEqPositiveFamily.lean#L7-L11

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

theorem GlobalTheory.sum_min_succ_eq_add_card {d : ℕ} (e : Fin d → ℕ) (j : ℕ) :
    ∑ i, min (j + 1) (e i) = ∑ i, min j (e i) + (Finset.univ.filter (fun i => j < e i)).card := by sorry
