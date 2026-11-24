-- Prove2me | Theorems.Thm_GlobalTheory_NewPrime_aeval_eq_zero_of_low_coeff_of_pow_eq_zero
-- name    : GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_pow_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:28.989889+00:00
-- url     : https://prove2.me/theorems/58dbe877-3e3c-4ed6-856a-8fd1b165ef45
-- title:
--   New Prime: aeval eq zero of low coeff of pow eq zero
-- statement:
--   The New Prime construction uses the aeval eq zero of low coeff of pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalEqZeroOfLowCoeffOfNilpotentMultiple.lean#L5-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalEqZeroOfLowCoeffOfNilpotentMultiple.lean#L5-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalEqZeroOfLowCoeffOfNilpotentMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NewPrime

theorem GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_pow_eq_zero :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t : B) (K : ℕ) (ξ : ι → B)
      (F : MvPolynomial ι O), t ^ K = 0 → (∀ q, t ∣ ξ q) →
      (∀ u : ι →₀ ℕ, u.degree < K → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by sorry
