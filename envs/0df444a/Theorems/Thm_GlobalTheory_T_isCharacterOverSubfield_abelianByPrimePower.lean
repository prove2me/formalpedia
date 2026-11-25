-- Prove2me | Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_abelianByPrimePower
-- name    : GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:37.626635+00:00
-- url     : https://prove2.me/theorems/0ec80b25-ddc0-464e-9114-e741a54e6a9d
-- title:
--   T: is Character Over Subfield abelian By Prime Power
-- statement:
--   The T construction uses the is Character Over Subfield abelian By Prime Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldAbelianByPrimePowerStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldAbelianByPrimePowerStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldAbelianByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldAbelianByPrimePowerStatement
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

theorem GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by sorry
