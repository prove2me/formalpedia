-- Prove2me | Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_of_virtual_and_character
-- name    : GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:58.387484+00:00
-- url     : https://prove2.me/theorems/3a6c25ed-c32b-40a8-9cb7-25d1c83680e5
-- title:
--   T: is Character Over Subfield of virtual and character
-- statement:
--   The T construction uses the is Character Over Subfield of virtual and character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfVirtualAndCharacterStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfVirtualAndCharacterStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfVirtualAndCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfVirtualAndCharacterStatement
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

theorem GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (χ : G → L), IsChar L L χ → χ ∈ Virt K L G → IsChar K L χ := by sorry
