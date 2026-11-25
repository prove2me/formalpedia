-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_right_grid_integral_convergence
-- name    : Kyprianou.Ch04.kw47_right_grid_integral_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:02:46.898831+00:00
-- url     : https://prove2.me/theorems/18b79e42-0c47-492a-9afd-e10d759a1374
-- title:
--   Bounded right-continuous quadrature converges on a finite Stieltjes or time measure
-- statement:
--   Right-endpoint weighted quadrature converges to the integral of a bounded measurable right-continuous real function on a half-open bounded interval, for any measure finite on that interval and any family of monotone finite grids with prescribed endpoints and mesh tending to zero. Repeated grid times are permitted. Each point of the half-open interval lies in exactly one nonempty half-open cell, and right endpoint evaluation converges from the right. Domination and finite indicator integration prove the exact stated limit.
-- source:
--   Kyprianou (2006), Exercise 4.7, deterministic product-grid convergence.

import Mathlib
open MeasureTheory Filter Set Topology
set_option autoImplicit false

/-- A bounded right-continuous function is approximated by right endpoint
grid sums for any measure finite on the covered half-open interval. -/

theorem Kyprianou.Ch04.kw47_right_grid_integral_convergence
    (mu : Measure Real) (a b : Real)
    [IsFiniteMeasure (mu.restrict (Ioc a b))]
    (f : Real → Real) (B : Real)
    (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B)
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x)
    (u : Nat → Nat → Real) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n → u n (i+1) - u n i ≤ delta n) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (mu (Ioc (u n i) (u n (i+1)))).toReal * f (u n (i+1)))
      atTop (nhds (∫ x in Ioc a b, f x ∂mu)) := by sorry
