-- Prove2me | Theorems.Thm_GlobalTheory_matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine
-- name    : GlobalTheory.matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:10:03.100377+00:00
-- url     : https://prove2.me/theorems/6130326d-fbc6-427b-85a5-e8b212a30b83
-- title:
--   Global Theory: matrix exp smul mul eq mul exp smul of intertwine
-- statement:
--   The Global Theory construction uses the matrix exp smul mul eq mul exp smul of intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixExpSmulMulEqMulExpSmulOfIntertwine.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixExpSmulMulEqMulExpSmulOfIntertwine.lean#L40-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixExpSmulMulEqMulExpSmulOfIntertwine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine :
    ∀ (m r : ℕ) (X : Matrix (Fin m) (Fin m) ℂ) (ε : Matrix (Fin m) (Fin r) ℂ)
      (β : Matrix (Fin r) (Fin r) ℂ), X * ε = ε * β →
      ∀ s : ℝ, NormedSpace.exp (s • X) * ε = ε * NormedSpace.exp (s • β) := by sorry
