-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_PsiPrimitive_res_top
-- name    : GlobalTheory.CuspGL.PsiPrimitive.res_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:59.614846+00:00
-- url     : https://prove2.me/theorems/60578aac-c708-4804-8b00-52c558b1c2c0
-- title:
--   Psi Primitive: res top
-- statement:
--   The Psi Primitive construction uses the res top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobi.lean#L53-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobi.lean#L53-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEqFinsumPsiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyTransversalSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveEndClassFunctionInvariantSubspaceMobi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
noncomputable section
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PsiPrimitive

theorem GlobalTheory.CuspGL.PsiPrimitive.res_top {F : Type} [Field F] (s : F[X] → ℂ) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (k : Module.End F V) : res s ⊤ k = psi s V k := by sorry
