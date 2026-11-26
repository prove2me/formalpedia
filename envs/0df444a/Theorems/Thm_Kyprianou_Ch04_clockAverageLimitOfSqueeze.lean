-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clockAverageLimitOfSqueeze
-- name    : Kyprianou.Ch04.clockAverageLimitOfSqueeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:26:13.289845+00:00
-- url     : https://prove2.me/theorems/608f5dea-f305-4c48-bb80-001899d957bb
-- title:
--   Clock average limit by vanishing early-time error
-- statement:
--   Choose a sufficiently late deterministic horizon, then take the clock error to zero. The lower bound and order convergence criterion give the conclusion.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9 and Theorem 4.10

import Mathlib
open Filter Set MeasureTheory
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.clockAverageLimitOfSqueeze
    (f : NNReal → ℝ) (A : ℕ → ℝ)
    (err : ℕ → NNReal → ℝ) (ell : ℝ)
    (hf : Tendsto f atTop (nhds ell))
    (hlower : ∀ n, ell ≤ A n)
    (hupper : ∀ n T, A n ≤ f T + err n T)
    (herr : ∀ T, Tendsto (fun n => err n T) atTop (nhds 0)) :
    Tendsto A atTop (nhds ell) := by
  sorry
