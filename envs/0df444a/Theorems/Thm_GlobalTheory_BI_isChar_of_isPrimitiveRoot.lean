-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_of_isPrimitiveRoot
-- name    : GlobalTheory.BI.isChar_of_isPrimitiveRoot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:02:24.414137+00:00
-- url     : https://prove2.me/theorems/573f8057-6db0-4cd1-a003-e58c3d4ac90e
-- title:
--   BI: is Char of is Primitive Root
-- statement:
--   The BI construction uses the is Char of is Primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharOfIsPrimitiveRoot.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharOfIsPrimitiveRoot.lean#L9-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldAbelianByPrimePowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfVirtualAndCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersOfAbelianByPrimePowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharOfIsPrimitiveRoot
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

theorem GlobalTheory.BI.isChar_of_isPrimitiveRoot : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by sorry
