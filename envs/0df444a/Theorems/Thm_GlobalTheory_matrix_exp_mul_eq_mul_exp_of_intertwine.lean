-- Prove2me | Theorems.Thm_GlobalTheory_matrix_exp_mul_eq_mul_exp_of_intertwine
-- name    : GlobalTheory.matrix_exp_mul_eq_mul_exp_of_intertwine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:41.859052+00:00
-- url     : https://prove2.me/theorems/a1ef4ce8-1afb-4c20-9c08-b25470dcb446
-- title:
--   Global Theory: matrix exp mul eq mul exp of intertwine
-- statement:
--   The Global Theory construction uses the matrix exp mul eq mul exp of intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixExpSmulMulEqMulExpSmulOfIntertwine.lean#L21-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixExpSmulMulEqMulExpSmulOfIntertwine.lean#L21-L38

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

theorem GlobalTheory.matrix_exp_mul_eq_mul_exp_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) :
    NormedSpace.exp X * ε = ε * NormedSpace.exp β := by sorry
