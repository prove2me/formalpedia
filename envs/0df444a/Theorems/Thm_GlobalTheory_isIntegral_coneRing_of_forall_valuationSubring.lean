-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_coneRing_of_forall_valuationSubring
-- name    : GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:57:10.702708+00:00
-- url     : https://prove2.me/theorems/09fc07e1-82d5-470f-8113-0010aa065bc2
-- title:
--   Global Theory: is Integral cone Ring of forall valuation Subring
-- statement:
--   The Global Theory construction uses the is Integral cone Ring of forall valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralConeRingOfForallValuationSubring.lean#L6-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralConeRingOfForallValuationSubring.lean#L6-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralConeRingOfForallValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory

theorem GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring :
    ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by sorry
