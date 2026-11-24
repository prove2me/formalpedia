-- Prove2me | Theorems.Thm_GlobalTheory_MonoTrace_ncard_pow_eq_one
-- name    : GlobalTheory.MonoTrace.ncard_pow_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:47.573802+00:00
-- url     : https://prove2.me/theorems/6983ec9c-dd10-4a31-be97-a2870cf76736
-- title:
--   Mono Trace: ncard pow eq one
-- statement:
--   The Mono Trace construction uses the ncard pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/TraceLiftMonomialMatrixEqSumEigenvalues.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/TraceLiftMonomialMatrixEqSumEigenvalues.lean#L10-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinrankEigenspaceMonomialMatrixLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumCharpolyRootsEqFinsumEigenspaceFinrankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_TraceLiftMonomialMatrixEqSumEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.MonoTrace

theorem GlobalTheory.MonoTrace.ncard_pow_eq_one (k : Type) [Field k] [IsAlgClosed k] (N : ℕ) (hN : (N : k) ≠ 0) :
    {μ : k | μ ^ N = 1}.Finite ∧ {μ : k | μ ^ N = 1}.ncard = N := by sorry
