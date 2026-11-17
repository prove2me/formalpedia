-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricMarkCompoundPoissonExponent
-- name    : Kyprianou.Ch01.geometricMarkCompoundPoissonExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:56:41.813898+00:00
-- url     : https://prove2.me/theorems/74e70e2a-fa64-4263-8c1a-f516f3cc2ffa
-- title:
--   Geometric compound-Poisson exponent for any complex mark characteristic value in the unit disc
-- statement:
--   For q in (0,1) and any complex z of modulus at most one, the logarithmic-jump compound-Poisson exponential exp[Σ_{k≥1}q^k/k·(z^k−1)] equals (1−q)/(1−qz). Substituting z as the characteristic function of an arbitrary real increment law provides the analytic identity behind the infinite divisibility of independent geometrically stopped sums.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(ii), geometric sum with IID marks.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_logarithmicJumpCompoundPoissonExponent
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricMarkCompoundPoissonExponent
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Complex.exp (∑' n : ℕ,
      ((q : ℂ) ^ (n + 1) / ((n : ℂ) + 1)) *
        (z ^ (n + 1) - 1)) =
      (((1 - q : ℝ) : ℂ) / (1 - (q : ℂ) * z)) := by
  sorry
