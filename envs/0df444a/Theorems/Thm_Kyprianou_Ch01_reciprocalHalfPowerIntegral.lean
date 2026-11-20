-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reciprocalHalfPowerIntegral
-- name    : Kyprianou.Ch01.reciprocalHalfPowerIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:13:26.484708+00:00
-- url     : https://prove2.me/theorems/2794aae0-37d6-46f0-bff2-9496b3b08e69
-- title:
--   Exact reciprocal-square-root substitution in a positive-halfline integral
-- statement:
--   The change of variable y=x^(-1/2) converts an integral over x>0 of x^(-3/2)*g(x^(-1/2)) to twice the integral of g over y>0. This uses the pinned generic integral_comp_rpow_Ioi with exponent -1/2, and avoids all inverse Gaussian assumptions.
-- source:
--   Mathlib.MeasureTheory.Integral.IntegralEqImproper integral_comp_rpow_Ioi (p=-1/2); Kyprianou 2006 inverse Gaussian density.

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.reciprocalHalfPowerIntegral (g : ℝ → ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
      x ^ (-(3 / 2 : ℝ)) * g (x ^ (-(1 / 2 : ℝ))) ∂volume) =
      2 * (∫ y in Set.Ioi (0 : ℝ), g y ∂volume) := by sorry
