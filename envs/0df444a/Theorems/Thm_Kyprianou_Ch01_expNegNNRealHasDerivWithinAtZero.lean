-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expNegNNRealHasDerivWithinAtZero
-- name    : Kyprianou.Ch01.expNegNNRealHasDerivWithinAtZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:12:16.780317+00:00
-- url     : https://prove2.me/theorems/966950aa-e8a2-4111-bce1-54f98a801e12
-- title:
--   Right derivative at zero of exponential survival through a nonnegative-time clock
-- statement:
--   For any real c, the real function t↦exp(-c*(Real.toNNReal t:ℝ)) restricted to t≥0 has right derivative -c at zero. Use the ordinary chain-rule derivative of exp(-c*t) and the equality Real.toNNReal t=t for nonnegative t. This is an independent elementary analytic helper.
-- source:
--   Mathlib real exponential chain rule and NNReal real-coercion identity, for the compound-Poisson first-event generator.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
open Real Set Filter
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.expNegNNRealHasDerivWithinAtZero
    (c : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ => Real.exp (-(c * (Real.toNNReal t : ℝ))))
      (-c) (Set.Ici 0) 0 := by
  sorry
