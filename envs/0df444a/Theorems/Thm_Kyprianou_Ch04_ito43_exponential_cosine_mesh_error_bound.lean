-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_exponential_cosine_mesh_error_bound
-- name    : Kyprianou.Ch04.ito43_exponential_cosine_mesh_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:52:41.172602+00:00
-- url     : https://prove2.me/theorems/f27fdd03-bd24-4c87-8386-465f7ab7b3d6
-- title:
--   Accumulated cosine exponential mesh error bound
-- statement:
--   The first-order exponential remainder at the mesh increment has norm at most its squared norm. Multiply its real-part error by the mesh count to bound the total by a constant divided by that count.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_exponential_cosine_mesh_error_bound (T : NNReal) (z : ℂ) (n : ℕ) (hn : 0 < n)
    (hs : (T:ℝ)*‖z‖/(n:ℝ) ≤ 1) :
    |(n:ℝ)*(1-(Complex.exp (((((T/(n:NNReal)):NNReal):ℝ):ℂ)*z)).re) -
      (-(T:ℝ)*z.re)| ≤ ((T:ℝ)*‖z‖)^2/(n:ℝ) := by sorry
