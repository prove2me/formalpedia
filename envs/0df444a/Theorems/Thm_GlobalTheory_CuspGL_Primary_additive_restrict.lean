-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_Primary_additive_restrict
-- name    : GlobalTheory.CuspGL.Primary.additive_restrict
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:51.761651+00:00
-- url     : https://prove2.me/theorems/867d85a7-21db-4637-a5ec-cbf39d236d4c
-- title:
--   Primary: additive restrict
-- statement:
--   The Primary construction uses the additive restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEq.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEq.lean#L33-L45

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

theorem GlobalTheory.CuspGL.Primary.additive_restrict {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {s : F[X] → ℂ} (hs : IsAdditive s) {g : Module.End F V} {f : F[X]} {m : ℕ} (hf : f.Monic)
    (hi : Irreducible f) (hc : LinearMap.charpoly g = f ^ m) (A : Submodule F V) (hA : ∀ x ∈ A, g x ∈ A) :
    (f.natDegree : ℂ) * s (LinearMap.charpoly (g.restrict hA)) = (Module.finrank F A : ℂ) * s f := by sorry
