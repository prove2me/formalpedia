-- Prove2me | Theorems.Thm_GlobalTheory_coeff_eq_zero_of_fourier_series_eq_zero
-- name    : GlobalTheory.coeff_eq_zero_of_fourier_series_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:09:44.545089+00:00
-- url     : https://prove2.me/theorems/d324479c-a546-4b73-8bf3-3fe593b7cde6
-- title:
--   Global Theory: coeff eq zero of fourier series eq zero
-- statement:
--   The Global Theory construction uses the coeff eq zero of fourier series eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffEqZeroOfHasSumMFourierOrthonormalImage.lean#L35-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffEqZeroOfHasSumMFourierOrthonormalImage.lean#L35-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffEqZeroOfHasSumMFourierOrthonormalImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
open GlobalTheory

theorem GlobalTheory.coeff_eq_zero_of_fourier_series_eq_zero :
    ∀ (J : Type) [Fintype J] (b : (J → ℤ) → ℂ), (Summable fun s => ‖b s‖) →
      (∀ x : J → ℝ, ∑' s, b s *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) = 0) →
      ∀ s, b s = 0 := by sorry
