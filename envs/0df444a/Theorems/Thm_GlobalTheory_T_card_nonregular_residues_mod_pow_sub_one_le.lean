-- Prove2me | Theorems.Thm_GlobalTheory_T_card_nonregular_residues_mod_pow_sub_one_le
-- name    : GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:42.684008+00:00
-- url     : https://prove2.me/theorems/1efad5bd-f372-45cc-9824-25756d624622
-- title:
--   T: card nonregular residues mod pow sub one le
-- statement:
--   The T construction uses the card nonregular residues mod pow sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardNonregularResiduesModPowSubOneLeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardNonregularResiduesModPowSubOneLeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardNonregularResiduesModPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardNonregularResiduesModPowSubOneLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le : ∀ q n : ℕ, 2 ≤ q → 0 < n → ((Finset.Ioo 0 (q ^ n - 1)).filter (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤ ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by sorry
