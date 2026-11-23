-- Prove2me | Theorems.Thm_GlobalTheory_MonoEigen_exists_back
-- name    : GlobalTheory.MonoEigen.exists_back
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:06.207513+00:00
-- url     : https://prove2.me/theorems/b1f7fba6-b80d-4adc-b481-7b7ee2f239df
-- title:
--   Mono Eigen: exists back
-- statement:
--   The Mono Eigen construction uses the exists back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L48-L51

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

theorem GlobalTheory.MonoEigen.exists_back (m : ℕ) (j : Fin n) : ∃ m' : ℕ, (σ ^ m') ((σ ^ m) j) = j := by sorry
