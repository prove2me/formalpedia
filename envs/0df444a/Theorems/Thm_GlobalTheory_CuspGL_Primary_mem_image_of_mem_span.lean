-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_Primary_mem_image_of_mem_span
-- name    : GlobalTheory.CuspGL.Primary.mem_image_of_mem_span
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:48.724387+00:00
-- url     : https://prove2.me/theorems/9a5ab9e2-d2b8-4251-be43-1076b25bc1f2
-- title:
--   Primary: mem image of mem span
-- statement:
--   The Primary construction uses the mem image of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEq.lean#L79-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEq.lean#L79-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.Primary

theorem GlobalTheory.CuspGL.Primary.mem_image_of_mem_span {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V)
    (f : F[X]) {t : ℕ} (π : V →ₗ[F] (Fin t → AdjoinRoot f)) (hπ : ∀ v, π (g v) = AdjoinRoot.root f • π v)
    (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (y : Fin t → AdjoinRoot f)
    (hy : y ∈ Submodule.span (AdjoinRoot f) (π '' W)) : ∃ w ∈ W, π w = y := by sorry
