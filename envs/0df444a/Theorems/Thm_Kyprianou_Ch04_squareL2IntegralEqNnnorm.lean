-- Prove2me | Theorems.Thm_Kyprianou_Ch04_squareL2IntegralEqNnnorm
-- name    : Kyprianou.Ch04.squareL2IntegralEqNnnorm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:10:46.448337+00:00
-- url     : https://prove2.me/theorems/0a0ab886-d60b-4167-b97d-ec77b5ef6917
-- title:
--   Real square integral equals ENNReal squared-norm lintegral toReal
-- statement:
--   For a real-valued random variable with integrable square, the real second moment agrees with the real conversion of the extended nonnegative squared-norm integral.
-- source:
--   Mathlib integral_eq_lintegral_of_nonneg_ae and elementary real squared norm; used for the finite predictable compensated Poisson integral isometry in Kyprianou (2006), Chapter 4, Exercise 4.4.

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch04.squareL2IntegralEqNnnorm

    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ)
    (hInt : Integrable (fun ω => (Z ω) ^ 2) P) :
    ∫ ω, (Z ω) ^ 2 ∂P =
      (∫⁻ ω, ((‖Z ω‖₊ : ℝ≥0∞) ^ 2) ∂P).toReal := by
  sorry
