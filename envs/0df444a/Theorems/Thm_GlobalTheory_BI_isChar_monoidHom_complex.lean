-- Prove2me | Theorems.Thm_GlobalTheory_BI_isChar_monoidHom_complex
-- name    : GlobalTheory.BI.isChar_monoidHom_complex
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:45.772714+00:00
-- url     : https://prove2.me/theorems/3d2c40e7-38f9-4e9b-885c-79735c9b8767
-- title:
--   BI: is Char monoid Hom complex
-- statement:
--   The BI construction uses the is Char monoid Hom complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharactersMulComapConjIndLinear.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharactersMulComapConjIndLinear.lean#L36-L44

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

theorem GlobalTheory.BI.isChar_monoidHom_complex {G : Type} [Group G] (lam : G →* ℂˣ) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (fun g => (lam g : ℂ)) := by sorry
