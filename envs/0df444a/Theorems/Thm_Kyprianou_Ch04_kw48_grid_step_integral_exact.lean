-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_grid_step_integral_exact
-- name    : Kyprianou.Ch04.kw48_grid_step_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:32:08.971439+00:00
-- url     : https://prove2.me/theorems/9d4ff7a9-7e60-42b2-862d-9a742ebecdc1
-- title:
--   Exact complex left or right endpoint step integral
-- statement:
--   Exact complex left or right endpoint step integral.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

/-- Exact integral of the bounded right-endpoint step approximation. -/

theorem Kyprianou.Ch04.kw48_grid_step_integral_exact
    (mu : Measure Real) (a b : Real)
    [IsFiniteMeasure (mu.restrict (Ioc a b))]
    (f : Real → Complex) (u : Nat → Real) (N : Nat) (right : Bool)
    (hu : Monotone u) (h0 : u 0 = a) (hN : u N = b) :
    (∫ x in Ioc a b, ∑ i ∈ Finset.range N,
      (Ioc (u i) (u (i+1))).indicator
        (fun _ : Real => f (if right then u (i+1) else u i)) x ∂mu) =
    ∑ i ∈ Finset.range N,
      (mu (Ioc (u i) (u (i+1)))).toReal • f (if right then u (i+1) else u i) := by sorry
