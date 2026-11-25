-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteGroupFunctionPairing_add_nat_pos_symm
-- name    : GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:24.285489+00:00
-- url     : https://prove2.me/theorems/d514f18e-3a4f-41c3-a13e-91d7f3ed95a5
-- title:
--   T: finite Group Function Pairing add nat pos symm
-- statement:
--   The T construction uses the finite Group Function Pairing add nat pos symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingAddNatPosSymmStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingAddNatPosSymmStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingAddNatPosSymm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingAddNatPosSymmStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ a b c : G → L, pair (a + b) c = pair a c + pair b c) ∧ (∀ a b : G → L, IsChar K L a → IsChar K L b → ∃ n : ℕ, pair a b = (n : L)) ∧ (∀ φ : G → L, IsIrrChar K L φ → ∃ n : ℕ, 0 < n ∧ pair φ φ = (n : L)) ∧ ∀ a b : G → L, pair a b = pair b a := by sorry
