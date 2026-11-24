-- Prove2me | Theorems.Thm_GlobalTheory_TransposeMulCommute_mul_transpose_eq_of_transpose_mul_eq
-- name    : GlobalTheory.TransposeMulCommute.mul_transpose_eq_of_transpose_mul_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:11.019766+00:00
-- url     : https://prove2.me/theorems/a4b27bff-804c-4a04-999a-0665ec6e4964
-- title:
--   Transpose Mul Commute: mul transpose eq of transpose mul eq
-- statement:
--   The Transpose Mul Commute construction uses the mul transpose eq of transpose mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MulTransposeEqOfTransposeMulEq.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MulTransposeEqOfTransposeMulEq.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MulTransposeEqOfTransposeMulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TransposeMulCommute

theorem GlobalTheory.TransposeMulCommute.mul_transpose_eq_of_transpose_mul_eq :
    ∀ {al : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ} {m : ℕ}, (1 : ℕ) ≤ m →
      Matrix.transpose al * al = (↑m : ℤ) • (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ) →
      al * Matrix.transpose al = (↑m : ℤ) • (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ) := by sorry
