-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_mul_complex
-- name    : GlobalTheory.BI.isChar_mul_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:01.305297+00:00
-- url     : https://prove2.me/theorems/a30d8cf5-0966-4bff-a0e6-1f3f72f24481
-- title:
--   BI: is Char mul complex
-- statement:
--   The BI construction uses the is Char mul complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharactersMulComapConjIndLinear.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharactersMulComapConjIndLinear.lean#L16-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInducedClassFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
open Polynomial

theorem GlobalTheory.BI.isChar_mul_complex {G : Type} [Group G] {a b : G → ℂ}
    (ha : _root_.GlobalTheory.BI.IsChar ℂ ℂ a) (hb : _root_.GlobalTheory.BI.IsChar ℂ ℂ b) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (a * b) := by sorry
