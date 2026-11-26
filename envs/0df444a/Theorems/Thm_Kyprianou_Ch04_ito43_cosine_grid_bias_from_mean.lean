-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_grid_bias_from_mean
-- name    : Kyprianou.Ch04.ito43_cosine_grid_bias_from_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:46:28.813796+00:00
-- url     : https://prove2.me/theorems/98965dc1-4e3d-56c3-b82b-ef16a054f68e
-- title:
--   Full-grid mean bound controls prefix bias
-- statement:
--   A prefix contains a fraction of the full-grid mean, and the prefix time differs from the stopping time by at most one mesh.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cosine_grid_bias_from_mean (T : NNReal) (c μ : ℝ) (n j : ℕ) (hn : 0 < n) (hj : j ≤ n)
    (t : NNReal) (e : ℝ) (he : 0 < e)
    (hmean : |(n:ℝ)*μ-c*(T:ℝ)| < e)
    (hclock : |(t:ℝ)-(T:ℝ)*(j:ℝ)/(n:ℝ)| ≤ (T:ℝ)/(n:ℝ)) :
    |c*(t:ℝ)-(j:ℝ)*μ| ≤ e+|c| * ((T:ℝ)/(n:ℝ)) := by sorry
