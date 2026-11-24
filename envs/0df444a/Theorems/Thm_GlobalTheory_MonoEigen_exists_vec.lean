-- Prove2me | Theorems.Thm_GlobalTheory_MonoEigen_exists_vec
-- name    : GlobalTheory.MonoEigen.exists_vec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:46.989468+00:00
-- url     : https://prove2.me/theorems/3ed8366e-ffda-46ba-bc42-c063c8136a51
-- title:
--   Mono Eigen: exists vec
-- statement:
--   The Mono Eigen construction uses the exists vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L61-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L61-L88

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

theorem GlobalTheory.MonoEigen.exists_vec {s : Fin n} (hs : GoodRep σ a s) :
    ∃ v : Fin n → K, (∀ j, v (σ j) = a j * v j) ∧ v s = 1 ∧
      ∀ t, GoodRep σ a t → t ≠ s → v t = 0 := by sorry
