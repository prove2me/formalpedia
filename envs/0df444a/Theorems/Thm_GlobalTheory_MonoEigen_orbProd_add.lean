-- Prove2me | Theorems.Thm_GlobalTheory_MonoEigen_orbProd_add
-- name    : GlobalTheory.MonoEigen.orbProd_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:28:04.724441+00:00
-- url     : https://prove2.me/theorems/5cab2c4a-0f24-4bdb-bfc0-97f8e9d8bcb2
-- title:
--   Mono Eigen: orb Prod add
-- statement:
--   The Mono Eigen construction uses the orb Prod add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L23-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinrankEigenspaceMonomialMatrixLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.MonoEigen
variable {K : Type} [Field K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)

theorem GlobalTheory.MonoEigen.orbProd_add (d m : ℕ) (j : Fin n) :
    orbProd σ a (d + m) j = orbProd σ a d j * orbProd σ a m ((σ ^ d) j) := by sorry
