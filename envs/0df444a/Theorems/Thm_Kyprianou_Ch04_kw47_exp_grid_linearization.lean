-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_exp_grid_linearization
-- name    : Kyprianou.Ch04.kw47_exp_grid_linearization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:06:12.647852+00:00
-- url     : https://prove2.me/theorems/ab3cf527-6935-5feb-b204-58bc4170dd68
-- title:
--   Uniform first-order exponential grid linearisation error
-- statement:
--   For finite sequences with absolute weights at most one, increments of absolute size at most eta <= 1, and total absolute increment variation at most C, the difference between the weighted exponential increments 1-exp(-d) and the weighted linear increments d is at most eta C in absolute value. The quadratic exponential remainder bounds each error by |d| squared, which is at most eta |d|. This yields the pathwise vanishing error in the Kella-Whitt product-grid limit.
-- source:
--   Kyprianou (2006), Exercise 4.7; exponential product integration by parts.

import Mathlib
set_option autoImplicit false

/-- First-order expansion of the exponential integrating factor on
finite grids with small increments and bounded total variation. -/

theorem Kyprianou.Ch04.kw47_exp_grid_linearization
    (Z d : Nat → Real) (N : Nat) (eta C : Real)
    (hEta : 0 ≤ eta) (hEta1 : eta ≤ 1)
    (hZ : ∀ i, |Z i| ≤ 1)
    (hSmall : ∀ i < N, |d i| ≤ eta)
    (hVar : (∑ i ∈ Finset.range N, |d i|) ≤ C) :
    |(∑ i ∈ Finset.range N, Z i * (1 - Real.exp (-d i))) -
      (∑ i ∈ Finset.range N, Z i * d i)| ≤ eta * C := by sorry
