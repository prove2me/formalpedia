-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_isPrimitive_of_isCuspChar
-- name    : GlobalTheory.CuspGL.isPrimitive_of_isCuspChar
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:21:22.391537+00:00
-- url     : https://prove2.me/theorems/8fb813c0-e151-54db-a5e1-53f8c8feadc1
-- title:
--   Cusp GL: is Primitive of is Cusp Char
-- statement:
--   The Cusp GL construction uses the is Primitive of is Cusp Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrrCharEqOneOfSubsingleton.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrrCharEqOneOfSubsingleton.lean#L34-L43

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

theorem GlobalTheory.CuspGL.isPrimitive_of_isCuspChar {F : Type} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}
    (χ : GL (Fin d) F → ℂ) (h : CuspElliptic.IsCuspChar χ) : IsPrimitive (extZero χ) := by sorry
