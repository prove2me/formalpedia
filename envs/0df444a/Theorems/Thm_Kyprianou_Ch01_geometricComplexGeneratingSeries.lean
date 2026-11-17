-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricComplexGeneratingSeries
-- name    : Kyprianou.Ch01.geometricComplexGeneratingSeries
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:32:19.85073+00:00
-- url     : https://prove2.me/theorems/8b31dc44-7598-4506-92b7-1e14d56ee2fd
-- title:
--   Exact complex geometric power series as a rational probability-generating function
-- statement:
--   For complex parameters p and z satisfying ‖(1-p)z‖ < 1, the absolutely convergent complex generating series ∑_{k≥0} p(1-p)^k z^k equals p/[1-(1-p)z]. This exact Fourier-ready summation is the analytic input for the geometric counting law characteristic function, which in turn is used to exhibit the compound Poisson logarithmic-series structure in Kyprianou (2006) Chapter 1 Exercise 1.2(i). The theorem includes the genuine analytic convergence condition.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.2(i), printed p. 26 and solution p. 299; pinned Mathlib tsum_geometric_of_norm_lt_one, tsum_mul_left.

import Mathlib
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricComplexGeneratingSeries (p z : ℂ)
    (hbound : ‖(1 - p) * z‖ < 1) :
    (∑' k : ℕ, p * (1 - p) ^ k * z ^ k) =
      p / (1 - (1 - p) * z) := by
  sorry
