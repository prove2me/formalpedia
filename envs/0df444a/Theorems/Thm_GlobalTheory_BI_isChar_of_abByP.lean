-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_of_abByP
-- name    : GlobalTheory.BI.isChar_of_abByP
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:39.841244+00:00
-- url     : https://prove2.me/theorems/d77dd60e-30ac-4ae8-af5f-638cef4dedd6
-- title:
--   BI: is Char of ab By P
-- statement:
--   The BI construction uses the is Char of ab By P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldAbelianByPrimePower.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldAbelianByPrimePower.lean#L12-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsAbelianByPrimePowerGroupSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldZeroAndAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrimStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldLinearOfPrimitiveRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldAbelianByPrimePower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.isChar_of_abByP : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by sorry
