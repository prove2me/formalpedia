-- Prove2me | Theorems.Thm_GlobalTheory_BI_exists_isChar_eq_add_of_pair_ne_zero
-- name    : GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:11.092891+00:00
-- url     : https://prove2.me/theorems/0296b12f-5d7e-4a6c-bbd1-bc0f8fe5668d
-- title:
--   BI: exists is Char eq add of pair ne zero
-- statement:
--   The BI construction uses the exists is Char eq add of pair ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIsCharEqAddOfPairNeZero.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIsCharEqAddOfPairNeZero.lean#L8-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingCharacterEqFinrankInteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterQuotientOfInjectiveIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIsCharEqAddOfPairNeZero
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

theorem GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (φ a : G → L), IsIrrChar K L φ → IsChar K L a → pair a φ ≠ 0 → ∃ c : G → L, IsChar K L c ∧ a = φ + c := by sorry
