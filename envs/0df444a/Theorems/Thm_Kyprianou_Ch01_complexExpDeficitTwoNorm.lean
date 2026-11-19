-- Prove2me | Theorems.Thm_Kyprianou_Ch01_complexExpDeficitTwoNorm
-- name    : Kyprianou.Ch01.complexExpDeficitTwoNorm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:54:04.171637+00:00
-- url     : https://prove2.me/theorems/750f1d9d-691c-4fa3-bb08-ba83cc68c773
-- title:
--   Left half-plane complex exponential deficit bounded by twice the input norm
-- statement:
--   For every complex z in the closed left half-plane, the modulus of exp(z)-1 is at most 2 times the modulus of z. For small z use the complex exponential remainder bound, and for large z bound exp(z) by 1 from Re z≤0.
-- source:
--   Kyprianou 2006 Chapter 1 stable Gamma fractional exponent, complex exponential integrability of the original compensated kernel.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.complexExpDeficitTwoNorm (z : ℂ) (hz : z.re ≤ 0) :
  ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  sorry
