-- Prove2me | Theorems.Thm_GlobalTheory_exists_int_matrix_transpose_mul_eq_smul_one
-- name    : GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:42.70295+00:00
-- url     : https://prove2.me/theorems/66f867e4-00db-407f-9487-b25934d7b513
-- title:
--   Global Theory: exists int matrix transpose mul eq smul one
-- statement:
--   The Global Theory construction uses the exists int matrix transpose mul eq smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntMatrixTransposeMulEqSmulOne.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIntMatrixTransposeMulEqSmulOne.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntMatrixTransposeMulEqSmulOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (s : ℕ) :
    ∃ x : Matrix (Fin 4) (Fin 4) ℤ, x.transpose * x = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
      x * x.transpose = (s : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by sorry
