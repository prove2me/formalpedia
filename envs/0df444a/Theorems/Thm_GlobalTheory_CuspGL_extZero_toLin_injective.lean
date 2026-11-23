-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_extZero_toLin_injective
-- name    : GlobalTheory.CuspGL.extZero_toLin_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:42.597626+00:00
-- url     : https://prove2.me/theorems/33babb07-bcfe-4f46-ab6e-ebf711b8f572
-- title:
--   Cusp GL: ext Zero to Lin injective
-- statement:
--   The Cusp GL construction uses the ext Zero to Lin injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/GeneralLinearFunctionExtendZeroEndProperties.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/GeneralLinearFunctionExtendZeroEndProperties.lean#L11-L12

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

theorem GlobalTheory.CuspGL.extZero_toLin_injective :
    Function.Injective fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by sorry
