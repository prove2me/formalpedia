-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_exp_grid_linearization_limit
-- name    : Kyprianou.Ch04.kw48_exp_grid_linearization_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:44:28.597284+00:00
-- url     : https://prove2.me/theorems/829a518c-edfc-43d5-b758-3a6be8105860
-- title:
--   Vanishing first order complex exponential grid error
-- statement:
--   Vanishing first order complex exponential grid error.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_grid_linearization
open Filter Set Topology
set_option autoImplicit false

/-- Continuous exponents of uniformly bounded grid variation admit
first-order linearisation along arbitrary vanishing-mesh grids. -/

theorem Kyprianou.Ch04.kw48_exp_grid_linearization_limit
    (a b : Real) (g : Real → Complex) (hg : ContinuousOn g (Icc a b))
    (u : Nat → Nat → Real) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n → u n (i+1) - u n i ≤ delta n)
    (Z : Nat → Nat → Complex) (hZ : ∀ n i, ‖Z n i‖ ≤ 1)
    (C : Real) (hC : 0 ≤ C)
    (hVar : ∀ n, (∑ i ∈ Finset.range (N n),
      ‖g (u n (i+1)) - g (u n i)‖) ≤ C) :
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (N n),
        Z n i * (1 - Complex.exp (-(g (u n (i+1)) - g (u n i))))) -
      (∑ i ∈ Finset.range (N n),
        Z n i * (g (u n (i+1)) - g (u n i))))
      atTop (nhds 0) := by sorry
