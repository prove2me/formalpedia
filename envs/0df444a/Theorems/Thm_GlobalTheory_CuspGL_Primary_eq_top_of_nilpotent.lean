-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_Primary_eq_top_of_nilpotent
-- name    : GlobalTheory.CuspGL.Primary.eq_top_of_nilpotent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:47.756627+00:00
-- url     : https://prove2.me/theorems/72120adf-b49a-43d1-a188-76b711bcd1a9
-- title:
--   Primary: eq top of nilpotent
-- statement:
--   The Primary construction uses the eq top of nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEq.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEq.lean#L47-L67

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

theorem GlobalTheory.CuspGL.Primary.eq_top_of_nilpotent {F V : Type} [Field F] [AddCommGroup V] [Module F V] (N : Module.End F V)
    {m : ℕ} (hN : N ^ m = 0) (W : Submodule F V) (hW : ∀ x ∈ W, N x ∈ W)
    (h : ∀ v, ∃ w ∈ W, ∃ u, v = w + N u) : W = ⊤ := by sorry
