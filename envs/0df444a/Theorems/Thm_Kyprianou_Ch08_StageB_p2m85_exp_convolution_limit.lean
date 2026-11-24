-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_exp_convolution_limit
-- name    : Kyprianou.Ch08.StageB.p2m85_exp_convolution_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T15:13:32.834675+00:00
-- url     : https://prove2.me/theorems/9b7ec1ae-c985-49a8-9fa9-6f7e98c9a0ee
-- title:
--   Exponential convolution of a bounded convergent function
-- statement:
--   Dominated convergence on the positive half-line against an integrable exponential kernel.
-- source:
--   Kyprianou (2006), Exercise 8.5(i), positive discount asymptotic.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem Kyprianou.Ch08.StageB.p2m85_exp_convolution_limit
    (f : ℝ → ℝ) (φ L : ℝ) (hφ : 0 < φ)
    (hf : Measurable f) (h0 : ∀ t, 0 ≤ f t)
    (hb : ∀ t, f t ≤ L) (hl : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun z : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-φ*t) * f (z-t))
      atTop (𝓝 (L/φ)) := by
  sorry
