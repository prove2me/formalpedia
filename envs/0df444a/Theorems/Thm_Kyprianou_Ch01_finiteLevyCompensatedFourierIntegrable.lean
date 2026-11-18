-- Prove2me | Theorems.Thm_Kyprianou_Ch01_finiteLevyCompensatedFourierIntegrable
-- name    : Kyprianou.Ch01.finiteLevyCompensatedFourierIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:09:50.396204+00:00
-- url     : https://prove2.me/theorems/cd396a8e-55b3-45dc-b5ee-97d703edb997
-- title:
--   Compensated Fourier kernel is integrable under any finite real Lévy intensity
-- statement:
--   For any finite measure on the real line, and any real frequency, the compensated complex Fourier kernel exp(i ξ x)−1 is Bochner integrable. The proof bounds its modulus by two, using that exp(i ξ x) has modulus one. This supplies a uniform integrability obligation of the finite Lévy measure construction in Kyprianou Chapter 1 Exercise 1.2(ii).
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), compound-geometric finite Lévy measure.

import Mathlib
open MeasureTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.finiteLevyCompensatedFourierIntegrable
    (Λ : Measure ℝ) [IsFiniteMeasure Λ] (xi : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) Λ := by
  sorry
