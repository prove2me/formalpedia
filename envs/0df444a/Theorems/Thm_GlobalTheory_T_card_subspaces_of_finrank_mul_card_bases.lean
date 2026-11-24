-- Prove2me | Theorems.Thm_GlobalTheory_T_card_subspaces_of_finrank_mul_card_bases
-- name    : GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:49.934039+00:00
-- url     : https://prove2.me/theorems/8ffd1e4a-6539-4c55-be0f-bf7aae862794
-- title:
--   T: card subspaces of finrank mul card bases
-- statement:
--   The T construction uses the card subspaces of finrank mul card bases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardSubspacesOfFinrankMulCardBasesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardSubspacesOfFinrankMulCardBasesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBases
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → Nat.card {W : Submodule F V // Module.finrank F W = a} * ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) = ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by sorry
