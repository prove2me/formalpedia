-- Prove2me | Theorems.Thm_Kyprianou_Ch01_randomIndexSLLNProductLimit
-- name    : Kyprianou.Ch01.randomIndexSLLNProductLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:50:55.622581+00:00
-- url     : https://prove2.me/theorems/529b2da5-42d0-4378-9bb8-91e9ac3a514a
-- title:
--   Random-index strong-law ratio composition with count rate
-- statement:
--   Deterministic random-index transfer: if empirical sums divided by index converge, a counting clock goes to infinity, and that count divided by physical time converges to a rate, then the time-normalised sum along the clock converges to the product of the two limits. The zero-index case is handled by S(0)=0, without assuming positive counts at finite times.
-- source:
--   Kyprianou (2006) Chapter 1 Section 1.3.4 compound-Poisson law of large numbers; general limit composition.

import Mathlib
open Filter
open scoped NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.randomIndexSLLNProductLimit
    (S : ℕ → ℝ) (N : ℝ≥0 → ℕ) (mu rate : ℝ)
    (hS0 : S 0 = 0)
    (hS : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * S n) atTop (𝓝 mu))
    (hN : Tendsto N atTop atTop)
    (hRate : Tendsto (fun t : ℝ≥0 => (N t : ℝ) / (1 + (t : ℝ)))
      atTop (𝓝 rate)) :
    Tendsto (fun t : ℝ≥0 => S (N t) / (1 + (t : ℝ)))
      atTop (𝓝 (mu * rate)) := by
  sorry
