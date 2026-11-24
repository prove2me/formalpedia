-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteGroupFunctionPairing_character_eq_finrank_intertwining
-- name    : GlobalTheory.T.finiteGroupFunctionPairing_character_eq_finrank_intertwining
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:17.00656+00:00
-- url     : https://prove2.me/theorems/e345b886-c406-4e92-8083-11d91cadc430
-- title:
--   T: finite Group Function Pairing character eq finrank intertwining
-- statement:
--   The T construction uses the finite Group Function Pairing character eq finrank intertwining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingCharacterEqFinrankInteStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteGroupFunctionPairingCharacterEqFinrankInteStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingCharacterEqFinrankInte
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingCharacterEqFinrankInteStatement
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

theorem GlobalTheory.T.finiteGroupFunctionPairing_character_eq_finrank_intertwining : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by sorry
