-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_height_tail_shift_integral
-- name    : Kyprianou.Ch08.StageB.p2m85_height_tail_shift_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T16:11:13.76198+00:00
-- url     : https://prove2.me/theorems/0a144b57-6897-492c-a354-1222e6891ce9
-- title:
--   Fixed-width integral of the excursion tail vanishes
-- statement:
--   Bound the absolute integral by the width times the tail at the lower endpoint.
-- source:
--   Kyprianou (2006), Exercise 8.5(i), zero-discount limits.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

theorem Kyprianou.Ch08.StageB.p2m85_height_tail_shift_integral
    (n : Measure ℝ) (hn : n (Ici (1 : ℝ)) < ⊤) (x : ℝ) :
    Tendsto (fun a : ℝ => ∫ t in (a-x)..a, (n (Ici t)).toReal)
      atTop (𝓝 0) := by
  sorry
