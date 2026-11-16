-- Prove2me | Theorems.Thm_Kyprianou_Ch01_exp_scaled_derivative_bound
-- name    : Kyprianou.Ch01.exp_scaled_derivative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T18:16:42.499014+00:00
-- url     : https://prove2.me/theorems/767529eb-69fa-4ec3-bfd7-0ff43bd54630
-- title:
--   Uniform Laplace exponential derivative bound for positive parameters
-- statement:
--   For each strictly positive delta and natural k, the derivative magnitude factor k exp(-z k) is bounded by one divided by delta, uniformly for all z at least delta. This is the crucial moment-free estimate used to prove uniform time-continuity of discrete-state branching Laplace semigroups. The proof uses the universal inequality x exp(-x) <= exp(-1).
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.11(iii); Laplace transform uniform continuity estimate

import Mathlib
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.exp_scaled_derivative_bound
    (delta : ℝ) (hd : 0 < delta) (k : ℕ) (z : ℝ) (hz : delta ≤ z) :
    (k : ℝ) * Real.exp (-z * (k : ℝ)) ≤ delta⁻¹ := by sorry
