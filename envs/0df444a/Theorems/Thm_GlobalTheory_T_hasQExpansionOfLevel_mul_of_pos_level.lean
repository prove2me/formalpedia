-- Prove2me | Theorems.Thm_GlobalTheory_T_hasQExpansionOfLevel_mul_of_pos_level
-- name    : GlobalTheory.T.hasQExpansionOfLevel_mul_of_pos_level
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:04.478923+00:00
-- url     : https://prove2.me/theorems/ffaf8c04-0de9-423d-8c58-6a35a354fd6b
-- title:
--   T: has QExpansion Of Level mul of pos level
-- statement:
--   The T construction uses the has QExpansion Of Level mul of pos level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelMulOfPosLevelStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelMulOfPosLevelStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevelStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasQExpansionOfLevel_mul_of_pos_level : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ * g τ) (conv a b) := by sorry
