-- Prove2me | Theorems.Thm_GlobalTheory_matrix_pow_mul_eq_mul_pow_of_intertwine
-- name    : GlobalTheory.matrix_pow_mul_eq_mul_pow_of_intertwine
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:09:46.647286+00:00
-- url     : https://prove2.me/theorems/6a3ec92f-798f-4a60-9457-b2d73cea6689
-- title:
--   Global Theory: matrix pow mul eq mul pow of intertwine
-- statement:
--   The Global Theory construction uses the matrix pow mul eq mul pow of intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixExpSmulMulEqMulExpSmulOfIntertwine.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixExpSmulMulEqMulExpSmulOfIntertwine.lean#L7-L13

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

theorem GlobalTheory.matrix_pow_mul_eq_mul_pow_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) (n : ℕ) :
    X ^ n * ε = ε * β ^ n := by sorry
