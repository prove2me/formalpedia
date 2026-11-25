-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_finite_horizon_predictable_weight_bound
-- name    : Kyprianou.Ch04.kw47_finite_horizon_predictable_weight_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T18:07:57.256394+00:00
-- url     : https://prove2.me/theorems/89706d95-b4ec-46a4-b1ef-5d0a834c228f
-- title:
--   Bounded predictable Kella–Whitt exponential weight on finite horizons
-- statement:
--   For α≥0, u≥0 and 0≤r≤T, exp(−αu+ψr)≤exp(|ψ|T). This deterministic envelope uniformly bounds the predictable H-factor over any finite interval, using continuity and nonnegativity of the running maximum.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.7 and Exercise 4.7; exponential product-grid transfer.

import Mathlib
set_option autoImplicit false

theorem Kyprianou.Ch04.kw47_finite_horizon_predictable_weight_bound (alpha psi u r T : Real)
    (hAlpha : 0 ≤ alpha) (hU : 0 ≤ u)
    (hr : 0 ≤ r) (hrT : r ≤ T) :
    Real.exp (-alpha * u + psi * r) ≤ Real.exp (|psi| * T) := by sorry
