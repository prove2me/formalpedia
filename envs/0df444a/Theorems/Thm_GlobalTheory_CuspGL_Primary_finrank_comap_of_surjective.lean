-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_Primary_finrank_comap_of_surjective
-- name    : GlobalTheory.CuspGL.Primary.finrank_comap_of_surjective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:32:06.362954+00:00
-- url     : https://prove2.me/theorems/2ac73d63-ae13-4071-85fa-7ad387765498
-- title:
--   Primary: finrank comap of surjective
-- statement:
--   The Primary construction uses the finrank comap of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEq.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEq.lean#L15-L22

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

theorem GlobalTheory.CuspGL.Primary.finrank_comap_of_surjective {F V U : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup U] [Module F U] (π : V →ₗ[F] U) (hπ : Function.Surjective π)
    (A : Submodule F U) :
    Module.finrank F (A.comap π) = Module.finrank F (LinearMap.ker π) + Module.finrank F A := by sorry
