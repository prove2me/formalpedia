-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_product_grid_transfer
-- name    : Kyprianou.Ch04.kw48_product_grid_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:25:51.741588+00:00
-- url     : https://prove2.me/theorems/c469513e-a305-5ebe-9711-c40c81b3cbaa
-- title:
--   Complex predictable grid limit from correction convergence
-- statement:
--   Complex predictable grid limit from correction convergence.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i), complex product-grid proof.

import Mathlib
open Filter Topology
set_option autoImplicit false

/-- A convergent right-point correction determines the predictable grid limit. -/

theorem Kyprianou.Ch04.kw48_product_grid_transfer (Q C : Nat → Complex) (Za Zb limit : Complex)
    (hGrid : ∀ n, Q n + C n = Zb - Za)
    (hLim : Tendsto C atTop (nhds limit)) :
    Tendsto Q atTop (nhds (Zb-Za-limit)) := by sorry
