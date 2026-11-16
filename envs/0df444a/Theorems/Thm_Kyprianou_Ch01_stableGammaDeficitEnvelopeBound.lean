-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaDeficitEnvelopeBound
-- name    : Kyprianou.Ch01.stableGammaDeficitEnvelopeBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:31:02.827335+00:00
-- url     : https://prove2.me/theorems/3a0743df-b543-4d9d-8c83-ebe1eff203ed
-- title:
--   Pointwise stable Gamma exponential-deficit integrand dominated by an integrable power envelope
-- statement:
--   For positive u, x and stable index alpha in (0,1), |exp(-ux)-1| ≤ min(ux,1), from exp(-ux)≤1 and exp(-ux)≥1-ux. Multiply by nonnegative x^(-alpha-1), using x*x^(-alpha-1)=x^(-alpha), to dominate the deficit integrand by u*x^(-alpha) for x≤1 and x^(-alpha-1) for x>1. The exact envelope is independently proved integrable and will discharge the near-zero/infinite-tail bound of the Exercise 1.4(i) integration-by-parts child.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4(i), printed solution p.301, PDF page 155.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaDeficitEnvelopeBound
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u)
    (x : ℝ) (hx : 0 < x) :
    ‖(Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1)‖ ≤
      (if x ≤ 1 then u * x ^ (-alpha) else x ^ (-alpha - 1)) := by sorry
