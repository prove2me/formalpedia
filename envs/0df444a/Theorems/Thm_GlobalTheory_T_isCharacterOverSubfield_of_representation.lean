-- Prove2me | Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_of_representation
-- name    : GlobalTheory.T.isCharacterOverSubfield_of_representation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:46.101681+00:00
-- url     : https://prove2.me/theorems/c72b1055-2001-48f0-8c36-bcb8fd18189e
-- title:
--   T: is Character Over Subfield of representation
-- statement:
--   The T construction uses the is Character Over Subfield of representation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentationStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentationStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentationStatement
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

theorem GlobalTheory.T.isCharacterOverSubfield_of_representation : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V), IsChar K L (fun g => algebraMap K L (ρ.character g)) ∧ (ρ.IsIrreducible → IsIrrChar K L (fun g => algebraMap K L (ρ.character g))) := by sorry
