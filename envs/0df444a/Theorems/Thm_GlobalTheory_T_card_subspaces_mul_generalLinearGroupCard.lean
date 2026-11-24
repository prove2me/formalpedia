-- Prove2me | Theorems.Thm_GlobalTheory_T_card_subspaces_mul_generalLinearGroupCard
-- name    : GlobalTheory.T.card_subspaces_mul_generalLinearGroupCard
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:28:20.107732+00:00
-- url     : https://prove2.me/theorems/d53e0fc3-0967-471c-b468-6676586c4bfa
-- title:
--   T: card subspaces mul general Linear Group Card
-- statement:
--   The T construction uses the card subspaces mul general Linear Group Card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardSubspacesMulGeneralLinearGroupCardStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardSubspacesMulGeneralLinearGroupCardStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCardStatement
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

theorem GlobalTheory.T.card_subspaces_mul_generalLinearGroupCard : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * (Nat.card F : ℂ) ^ (a * (Module.finrank F V - a)) * glCard F a * glCard F (Module.finrank F V - a) = glCard F (Module.finrank F V) := by sorry
