-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_exp_grid_linearization
-- name    : Kyprianou.Ch04.kw48_exp_grid_linearization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:36:14.837698+00:00
-- url     : https://prove2.me/theorems/5b636c81-c84d-5b7a-9640-e743179bac70
-- title:
--   Uniform first order complex exponential grid approximation
-- statement:
--   Uniform first order complex exponential grid approximation.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw48_exp_remainder
set_option autoImplicit false

/-- Uniform quadratic control of the complex exponential grid error. -/

theorem Kyprianou.Ch04.kw48_exp_grid_linearization (Z d : Nat → Complex) (N : Nat) (eta C : Real)
    (hEta : 0 ≤ eta) (hEta1 : eta ≤ 1)
    (hZ : ∀ i, ‖Z i‖ ≤ 1)
    (hSmall : ∀ i < N, ‖d i‖ ≤ eta)
    (hVar : (∑ i ∈ Finset.range N, ‖d i‖) ≤ C) :
    ‖(∑ i ∈ Finset.range N, Z i * (1-Complex.exp (-d i))) -
      (∑ i ∈ Finset.range N, Z i * d i)‖ ≤ eta*C := by sorry
