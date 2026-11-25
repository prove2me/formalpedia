-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_isIrrChar_of_norm_one
-- name    : GlobalTheory.CuspGL.isIrrChar_of_norm_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:13:02.975139+00:00
-- url     : https://prove2.me/theorems/24f5c208-6a9e-550e-8a31-55b9d4392adb
-- title:
--   Cusp GL: is Irr Char of norm one
-- statement:
--   The Cusp GL construction uses the is Irr Char of norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrrCharEqOneOfSubsingleton.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrrCharEqOneOfSubsingleton.lean#L26-L32

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqOfIsPrimitiveOfEqOnEllipticFiniteGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleOfVirtualCharacterNormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrrCharEqOneOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.isIrrChar_of_norm_one {G : Type} [Group G] [Fintype G] (χ : G → ℂ)
    (h : CuspElliptic.IsIrrChar χ) : GlobalTheory.BI.IsIrrChar ℂ ℂ χ := by sorry
