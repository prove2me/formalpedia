-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_large_prime_sq_dvd_eval_of_separable
-- name    : GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:27.104024+00:00
-- url     : https://prove2.me/theorems/928eedcb-17bd-4329-9bd0-3222730cf6d4
-- title:
--   T: exists large prime sq dvd eval of separable
-- statement:
--   The T construction uses the exists large prime sq dvd eval of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SepIntPolyRootModPrimeSqStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SepIntPolyRootModPrimeSqStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSqStatement
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

theorem GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable : ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by sorry
