-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_height_tail_zero
-- name    : Kyprianou.Ch08.StageB.p2m85_height_tail_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T16:11:13.137551+00:00
-- url     : https://prove2.me/theorems/29bb873c-1c2f-4dec-963c-58a2555d1e61
-- title:
--   Finite excursion height tail vanishes
-- statement:
--   Continuity from above on decreasing closed upper rays with finite mass.
-- source:
--   Kyprianou (2006), Exercise 8.5(i), zero-discount limits.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

theorem Kyprianou.Ch08.StageB.p2m85_height_tail_zero
    (n : Measure ℝ) (hn : n (Ici (1 : ℝ)) < ⊤) :
    Tendsto (fun t : ℝ => (n (Ici t)).toReal) atTop (𝓝 0) := by
  sorry
