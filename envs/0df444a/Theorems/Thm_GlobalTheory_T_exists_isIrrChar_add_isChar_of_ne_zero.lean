-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isIrrChar_add_isChar_of_ne_zero
-- name    : GlobalTheory.T.exists_isIrrChar_add_isChar_of_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:09.632295+00:00
-- url     : https://prove2.me/theorems/75a26a4c-fc76-49e6-ac14-f4989716b7e2
-- title:
--   T: exists is Irr Char add is Char of ne zero
-- statement:
--   The T construction uses the exists is Irr Char add is Char of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIrrCharAddStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIrrCharAddStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIrrCharAdd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIrrCharAddStatement
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

theorem GlobalTheory.T.exists_isIrrChar_add_isChar_of_ne_zero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by sorry
