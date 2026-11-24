-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteGroupFunctionPairing_self_irreducible_algClosed
-- name    : GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:21.00419+00:00
-- url     : https://prove2.me/theorems/c878f0d9-6595-4a24-b1bd-4118145c4784
-- title:
--   T: finite Group Function Pairing self irreducible alg Closed
-- statement:
--   The T construction uses the finite Group Function Pairing self irreducible alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
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

theorem GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), IsIrrChar L L χ → pair χ χ = 1 := by sorry
