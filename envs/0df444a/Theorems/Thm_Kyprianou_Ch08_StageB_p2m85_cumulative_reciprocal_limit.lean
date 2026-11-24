-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_cumulative_reciprocal_limit
-- name    : Kyprianou.Ch08.StageB.p2m85_cumulative_reciprocal_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:59:13.799949+00:00
-- url     : https://prove2.me/theorems/a978ed92-2fbc-4be1-ad62-c1562403acc1
-- title:
--   Invert the increasing cumulative measure in extended nonnegative reals, then multiply by the inverse exponential tilt.
-- statement:
--   Invert the increasing cumulative measure in extended nonnegative reals, then multiply by the inverse exponential tilt.
-- source:
--   Kyprianou (2006), Exercise 8.5(i)

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.p2m85_cumulative_reciprocal_limit
    (ν : Measure ℝ) (V : ℝ → ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hfin : ∀ z : ℝ, ν (Iic z) < ⊤) (hpos : ν univ ≠ 0)
    (hV : ∀ z : ℝ, Real.exp (-φ*z)*V z = (ν (Iic z)).toReal) :
    Tendsto (fun z : ℝ => (V z)⁻¹) atTop
      (𝓝 (if φ = 0 then ((ν univ)⁻¹).toReal else 0)) := by
  sorry
