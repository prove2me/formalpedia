-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_gt_dvd_eval
-- name    : GlobalTheory.exists_prime_gt_dvd_eval
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:42.710319+00:00
-- url     : https://prove2.me/theorems/f01a1d90-8a71-4e95-b35c-ae059716f110
-- title:
--   Global Theory: exists prime gt dvd eval
-- statement:
--   The Global Theory construction uses the exists prime gt dvd eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLargePrimeDvdIntPolynomialEval.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLargePrimeDvdIntPolynomialEval.lean#L9-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeGtDvdEval
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEval
import Theorems.Thm_GlobalTheory_PrimeDivisorOfPolynomialValue_exists_prime_gt_dvd_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
open Polynomial

theorem GlobalTheory.exists_prime_gt_dvd_eval :
    ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by sorry
