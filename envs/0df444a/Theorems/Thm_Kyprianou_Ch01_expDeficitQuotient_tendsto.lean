-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expDeficitQuotient_tendsto
-- name    : Kyprianou.Ch01.expDeficitQuotient_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T12:12:51.585948+00:00
-- url     : https://prove2.me/theorems/82f7aabc-e939-4827-9344-29bcb3c72bb1
-- title:
--   Pointwise right limit of exponential-deficit quotient
-- statement:
--   The right limit of (1−exp(−θx))/θ as θ→0 is x, by the derivative of exp at zero.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9(i): right Laplace derivative and dominated convergence

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.expDeficitQuotient_tendsto
    (x : ℝ) :
    Tendsto (fun theta : ℝ => (1 - Real.exp (-theta * x)) / theta)
      (𝓝[>] (0 : ℝ)) (𝓝 x) := by sorry
