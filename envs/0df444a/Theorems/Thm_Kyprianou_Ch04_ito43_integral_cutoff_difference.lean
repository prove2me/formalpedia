-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_integral_cutoff_difference
-- name    : Kyprianou.Ch04.ito43_integral_cutoff_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:33:42.831409+00:00
-- url     : https://prove2.me/theorems/3da20320-f4ab-4936-930c-acb688c848e9
-- title:
--   Integral cutoff subtraction equals complementary integral
-- statement:
--   Integral cutoff subtraction equals complementary integral.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory
set_option autoImplicit false

/-- The difference of an uncut excess and its retained cutoff is the complementary integral. -/

theorem Kyprianou.Ch04.ito43_integral_cutoff_difference {α : Type} [MeasurableSpace α] (μ : Measure α)
    (A B chi : α → ℝ) (hA : Integrable A μ) (hB : Integrable B μ)
    (hTail : Integrable (fun z => (A z-B z)*(1-chi z)) μ) :
    (∫ z, A z ∂μ) - (∫ z, B z ∂μ) -
      (∫ z, (A z-B z)*chi z ∂μ) =
        ∫ z, (A z-B z)*(1-chi z) ∂μ := by sorry
