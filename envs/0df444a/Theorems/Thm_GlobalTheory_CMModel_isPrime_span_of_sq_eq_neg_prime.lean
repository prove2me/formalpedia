-- Prove2me | Theorems.Thm_GlobalTheory_CMModel_isPrime_span_of_sq_eq_neg_prime
-- name    : GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:04:37.731837+00:00
-- url     : https://prove2.me/theorems/d484c985-d5b6-487b-af73-7a25d4313c29
-- title:
--   CMModel: is Prime span of sq eq neg prime
-- statement:
--   The CMModel construction uses the is Prime span of sq eq neg prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsPrimeSpanOfSqEqNegPrime.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsPrimeSpanOfSqEqNegPrime.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsPrimeSpanOfSqEqNegPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CMModel

theorem GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime :
    ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 →
      y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by sorry
