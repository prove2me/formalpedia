-- Prove2me | Theorems.Thm_Kyprianou_Ch04_geometricWorkloadResolventArithmetic
-- name    : Kyprianou.Ch04.geometricWorkloadResolventArithmetic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:45.952851+00:00
-- url     : https://prove2.me/theorems/257328c9-4b86-5ac8-b33e-e2983a76c446
-- title:
--   The normalized tail geometric resolvent reduces to the workload Laplace ratio.
-- statement:
--   The normalized tail geometric resolvent reduces to the workload Laplace ratio.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.geometricWorkloadResolventArithmetic (r : ENNReal) (d a p : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hd : 0 < d) (ha : 0 < a)
    (hp : 0 < p) (hgap : p ≤ d*a) :
    ((1-r) * (1-r*((ENNReal.ofReal d*r)⁻¹ *
        ENNReal.ofReal ((d*a-p)/a)))⁻¹).toReal =
      (d-d*r.toReal)*a/p := by
  sorry
