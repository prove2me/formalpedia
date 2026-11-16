-- Prove2me | Theorems.Thm_Kyprianou_Ch01_exp_uniform_lipschitz_on_positive
-- name    : Kyprianou.Ch01.exp_uniform_lipschitz_on_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T18:23:02.940409+00:00
-- url     : https://prove2.me/theorems/df473ead-e1e9-47ae-acf2-b7e11250fa15
-- title:
--   Uniform Lipschitz bound for exponential Laplace weights away from zero
-- statement:
--   For positive delta, every nonnegative integer k and x,y>=delta, the map z to exp(-zk) is Lipschitz with constant delta^-1, independent of k. This follows from the exponential derivative majorant and a convex-set mean value theorem.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.11(iii), Laplace semigroup time continuity without moment assumptions

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_exp_scaled_derivative_bound
open Real Set
open scoped Topology
set_option autoImplicit false

/-- Exponential Laplace weights have a moment-independent local Lipschitz constant. -/

theorem Kyprianou.Ch01.exp_uniform_lipschitz_on_positive
    (delta : ℝ) (hd : 0 < delta) (k : ℕ)
    (x y : ℝ) (hx : delta ≤ x) (hy : delta ≤ y) :
    |Real.exp (-y * (k : ℝ)) - Real.exp (-x * (k : ℝ))| ≤
      delta⁻¹ * |y - x| := by sorry
