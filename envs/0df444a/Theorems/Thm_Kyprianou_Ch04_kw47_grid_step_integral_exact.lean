-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_grid_step_integral_exact
-- name    : Kyprianou.Ch04.kw47_grid_step_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:05:28.893428+00:00
-- url     : https://prove2.me/theorems/e00485d2-6b9e-5b3b-9d98-f575025a3a32
-- title:
--   Exact integration of finite right-endpoint cell step functions
-- statement:
--   A monotone finite grid with initial endpoint a and terminal endpoint b partitions the half-open interval Ioc(a,b). Integrating its right-endpoint indicator step function under a measure finite on this interval gives exactly the finite sum of right-endpoint values weighted by cell masses.
-- source:
--   Kyprianou (2006), Exercise 4.7; deterministic grid quadrature.

import Mathlib
open MeasureTheory Set
set_option autoImplicit false

/-- Exact integral of the bounded right-endpoint step approximation. -/

theorem Kyprianou.Ch04.kw47_grid_step_integral_exact
    (mu : Measure Real) (a b : Real)
    [IsFiniteMeasure (mu.restrict (Ioc a b))]
    (f : Real → Real) (u : Nat → Real) (N : Nat)
    (hu : Monotone u) (h0 : u 0 = a) (hN : u N = b) :
    (∫ x in Ioc a b, ∑ i ∈ Finset.range N,
      (Ioc (u i) (u (i+1))).indicator
        (fun _ : Real => f (u (i+1))) x ∂mu) =
    ∑ i ∈ Finset.range N,
      (mu (Ioc (u i) (u (i+1)))).toReal * f (u (i+1)) := by sorry
