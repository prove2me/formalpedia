-- Prove2me | Theorems.Thm_GlobalTheory_MonoEigen_apply_pow
-- name    : GlobalTheory.MonoEigen.apply_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:41.906844+00:00
-- url     : https://prove2.me/theorems/84494820-2ec1-411b-9f55-aac7a07a4902
-- title:
--   Mono Eigen: apply pow
-- statement:
--   The Mono Eigen construction uses the apply pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L41-L46

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

theorem GlobalTheory.MonoEigen.apply_pow {v : Fin n → K} (hv : ∀ j, v (σ j) = a j * v j) (m : ℕ) (j : Fin n) :
    v ((σ ^ m) j) = orbProd σ a m j * v j := by sorry
