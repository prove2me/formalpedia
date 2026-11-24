-- Prove2me | Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_linear_of_primitiveRoot
-- name    : GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:44.228803+00:00
-- url     : https://prove2.me/theorems/fc19a893-779d-479a-85ad-3ff0af06e692
-- title:
--   T: is Character Over Subfield linear of primitive Root
-- statement:
--   The T construction uses the is Character Over Subfield linear of primitive Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldLinearOfPrimitiveRootStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldLinearOfPrimitiveRootStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldLinearOfPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldLinearOfPrimitiveRootStatement
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

theorem GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by sorry
