-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_mem_virt_complex
-- name    : GlobalTheory.BI.isChar_mem_virt_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:54.255802+00:00
-- url     : https://prove2.me/theorems/8408585c-2391-4a22-98b2-bb8538cab60c
-- title:
--   BI: is Char mem virt complex
-- statement:
--   The BI construction uses the is Char mem virt complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharactersMulComapConjIndLinear.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharactersMulComapConjIndLinear.lean#L11-L13

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

theorem GlobalTheory.BI.isChar_mem_virt_complex {G : Type} [Group G] {χ : G → ℂ}
    (h : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ) : χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G := by sorry
