-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_integral_relation_C_mul_X_pow_of_valuationSubring
-- name    : GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:22.419685+00:00
-- url     : https://prove2.me/theorems/fd3c7f96-68be-4b15-bf9d-6c7d59c7c315
-- title:
--   T: exists integral relation C mul X pow of valuation Subring
-- statement:
--   The T construction uses the exists integral relation C mul X pow of valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralConeRingOfForallValuationSubringStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralConeRingOfForallValuationSubringStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralConeRingOfForallValuationSubring
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralConeRingOfForallValuationSubringStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by sorry
