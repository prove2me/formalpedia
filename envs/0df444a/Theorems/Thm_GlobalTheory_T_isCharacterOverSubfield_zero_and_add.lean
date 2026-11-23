-- Prove2me | Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_zero_and_add
-- name    : GlobalTheory.T.isCharacterOverSubfield_zero_and_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:56.522866+00:00
-- url     : https://prove2.me/theorems/647a31fb-513e-4eda-bcc0-4cd0110de068
-- title:
--   T: is Character Over Subfield zero and add
-- statement:
--   The T construction uses the is Character Over Subfield zero and add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldZeroAndAddStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldZeroAndAddStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldZeroAndAdd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldZeroAndAddStatement
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

theorem GlobalTheory.T.isCharacterOverSubfield_zero_and_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G], IsChar K L (0 : G → L) ∧ ∀ a b : G → L, IsChar K L a → IsChar K L b → IsChar K L (a + b) := by sorry
