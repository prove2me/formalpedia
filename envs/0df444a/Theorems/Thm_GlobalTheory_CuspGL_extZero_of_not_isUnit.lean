-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_extZero_of_not_isUnit
-- name    : GlobalTheory.CuspGL.extZero_of_not_isUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:49.536565+00:00
-- url     : https://prove2.me/theorems/57216bdf-0f7d-4da9-ac63-bb5b0e762d11
-- title:
--   Cusp GL: ext Zero of not is Unit
-- statement:
--   The Cusp GL construction uses the ext Zero of not is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/GeneralLinearFunctionExtendZeroEndProperties.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/GeneralLinearFunctionExtendZeroEndProperties.lean#L33-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_GeneralLinearFunctionExtendZeroEndProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] {d : ℕ}

theorem GlobalTheory.CuspGL.extZero_of_not_isUnit (χ : GL (Fin d) F → ℂ) (g : Module.End F (Fin d → F))
    (hg : ¬ IsUnit g) : extZero χ g = 0 := by sorry
