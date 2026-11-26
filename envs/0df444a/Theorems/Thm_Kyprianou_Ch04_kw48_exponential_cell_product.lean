-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_exponential_cell_product
-- name    : Kyprianou.Ch04.kw48_exponential_cell_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:25:51.249819+00:00
-- url     : https://prove2.me/theorems/713f0d3f-ac9e-58d2-b530-c65d81ea46d7
-- title:
--   Complex exponential right-point product correction
-- statement:
--   Complex exponential right-point product correction.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i), complex product-grid proof.

import Mathlib
set_option autoImplicit false

/-- Right-point product correction expressed through the logarithmic increment. -/

theorem Kyprianou.Ch04.kw48_exponential_cell_product (eb ga gb : Complex) :
    Complex.exp eb * (Complex.exp gb - Complex.exp ga) =
      Complex.exp (eb + gb) * (1 - Complex.exp (-(gb - ga))) := by sorry
