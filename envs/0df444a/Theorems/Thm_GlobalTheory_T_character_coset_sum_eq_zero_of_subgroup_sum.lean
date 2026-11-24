-- Prove2me | Theorems.Thm_GlobalTheory_T_character_coset_sum_eq_zero_of_subgroup_sum
-- name    : GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:27.534669+00:00
-- url     : https://prove2.me/theorems/5b74a98c-1614-4f97-b1ff-fb37321a48c9
-- title:
--   T: character coset sum eq zero of subgroup sum
-- statement:
--   The T construction uses the character coset sum eq zero of subgroup sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharacterCosetSumEqZeroOfSubgroupSumStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharacterCosetSumEqZeroOfSubgroupSumStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterCosetSumEqZeroOfSubgroupSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterCosetSumEqZeroOfSubgroupSumStatement
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

theorem GlobalTheory.T.character_coset_sum_eq_zero_of_subgroup_sum : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsChar ℂ ℂ χ → ∀ H : Subgroup G, ∑ᶠ u : H, χ u = 0 → ∀ g : G, ∑ᶠ u : H, χ (g * u) = 0 := by sorry
