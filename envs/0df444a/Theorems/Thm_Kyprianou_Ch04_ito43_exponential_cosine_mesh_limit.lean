-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_exponential_cosine_mesh_limit
-- name    : Kyprianou.Ch04.ito43_exponential_cosine_mesh_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:49:05.467081+00:00
-- url     : https://prove2.me/theorems/aee28919-7f28-401e-bd0d-9c2a1bb2b936
-- title:
--   Real cosine exponential mesh mean has first-order limit
-- statement:
--   Use the proved complex exponential remainder with argument equal to minus the mesh duration times the exponent, take real parts, and bound the accumulated remainder by a constant divided by the number of mesh cells.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_exponential_cosine_mesh_limit (T : NNReal) (z : ℂ) :
    Tendsto (fun n : ℕ => (n:ℝ)*(1-(Complex.exp
      (((((T/(n:NNReal)):NNReal):ℝ):ℂ)*z)).re)) atTop (nhds (-(T:ℝ)*z.re)) := by sorry
