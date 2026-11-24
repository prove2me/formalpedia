-- Prove2me | Theorems.Thm_GlobalTheory_MonoEigen_mem_eigenspace_iff
-- name    : GlobalTheory.MonoEigen.mem_eigenspace_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:56.271801+00:00
-- url     : https://prove2.me/theorems/399fc720-b9b2-46b5-8bf3-f19f86ad4014
-- title:
--   Mono Eigen: mem eigenspace iff
-- statement:
--   The Mono Eigen construction uses the mem eigenspace iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L128-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinrankEigenspaceMonomialMatrixLift.lean#L128-L142

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

theorem GlobalTheory.MonoEigen.mem_eigenspace_iff (c : Fin n → K) (μ : K) (hμ : μ ≠ 0) (v : Fin n → K) :
    v ∈ Module.End.eigenspace
      (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ ↔
      ∀ j, v (σ j) = (c j * μ⁻¹) * v j := by sorry
