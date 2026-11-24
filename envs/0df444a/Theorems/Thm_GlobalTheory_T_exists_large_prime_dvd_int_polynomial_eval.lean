-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_large_prime_dvd_int_polynomial_eval
-- name    : GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:03.901949+00:00
-- url     : https://prove2.me/theorems/6f279054-7ba4-4a58-b32f-62433d328146
-- title:
--   T: exists large prime dvd int polynomial eval
-- statement:
--   The T construction uses the exists large prime dvd int polynomial eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLargePrimeDvdIntPolynomialEvalStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLargePrimeDvdIntPolynomialEvalStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEval
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEvalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval : ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by sorry
