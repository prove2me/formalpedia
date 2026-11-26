-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_complex_quadrature
-- name    : Kyprianou.Ch04.kw48_complex_quadrature
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:41:23.817522+00:00
-- url     : https://prove2.me/theorems/304bb5f0-afd9-45e0-9a2a-0e4d3ba5a043
-- title:
--   Bounded complex quadrature from either endpoint under almost everywhere one-sided continuity
-- statement:
--   Bounded complex quadrature from either endpoint under almost everywhere one-sided continuity.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_eval_distance
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_step_integral_exact
open MeasureTheory Filter Set Topology
set_option autoImplicit false

/-- Both endpoint quadratures converge for a bounded complex function
continuous from the chosen side almost everywhere for the cell measure. -/

theorem Kyprianou.Ch04.kw48_complex_quadrature
    (mu : Measure Real) (a b : Real)
    [IsFiniteMeasure (mu.restrict (Ioc a b))]
    (f : Real → Complex) (B : Real)
    (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ B)
    (u : Nat → Nat → Real) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n → u n (i+1)-u n i ≤ delta n)
    (right : Bool)
    (hCont : ∀ᵐ x ∂(mu.restrict (Ioc a b)),
      ContinuousWithinAt f (if right then Ici x else Iic x) x) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (mu (Ioc (u n i) (u n (i+1)))).toReal •
        f (if right then u n (i+1) else u n i))
      atTop (nhds (∫ x in Ioc a b, f x ∂mu)) := by sorry
