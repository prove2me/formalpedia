-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_irrChar_eq_one_of_subsingleton
-- name    : GlobalTheory.CuspGL.irrChar_eq_one_of_subsingleton
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:26:42.061163+00:00
-- url     : https://prove2.me/theorems/499b04af-6284-4469-b7fa-94a9f02ea40d
-- title:
--   Cusp GL: irr Char eq one of subsingleton
-- statement:
--   The Cusp GL construction uses the irr Char eq one of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrrCharEqOneOfSubsingleton.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrrCharEqOneOfSubsingleton.lean#L12-L24

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

theorem GlobalTheory.CuspGL.irrChar_eq_one_of_subsingleton {G : Type} [Group G] [Fintype G] [Subsingleton G] (χ : G → ℂ)
    (h : CuspElliptic.IsIrrChar χ) (x : G) : χ x = 1 := by sorry
