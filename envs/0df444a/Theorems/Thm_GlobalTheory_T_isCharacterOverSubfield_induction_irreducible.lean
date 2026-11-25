-- Prove2me | Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_induction_irreducible
-- name    : GlobalTheory.T.isCharacterOverSubfield_induction_irreducible
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:31.294375+00:00
-- url     : https://prove2.me/theorems/213b4813-f1d2-4a89-b7c2-97c39eb2dd87
-- title:
--   T: is Character Over Subfield induction irreducible
-- statement:
--   The T construction uses the is Character Over Subfield induction irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldInductionIrreducibleStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldInductionIrreducibleStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducibleStatement
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

theorem GlobalTheory.T.isCharacterOverSubfield_induction_irreducible : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (Q : (G → L) → Prop), Q 0 → (∀ φ c : G → L, IsIrrChar K L φ → IsChar K L c → Q c → Q (φ + c)) → ∀ a : G → L, IsChar K L a → Q a := by sorry
