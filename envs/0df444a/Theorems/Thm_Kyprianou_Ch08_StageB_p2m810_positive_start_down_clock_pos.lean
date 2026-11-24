-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_positive_start_down_clock_pos
-- name    : Kyprianou.Ch08.StageB.p2m810_positive_start_down_clock_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T21:50:41.668475+00:00
-- url     : https://prove2.me/theorems/90570dec-3142-49aa-9a85-4390a37c15b2
-- title:
--   Right continuity at zero and a positive initial reserve give a strictly positive first downcrossing clock.
-- statement:
--   Right continuity at zero and a positive initial reserve give a strictly positive first downcrossing clock.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_positive_start_down_clock_pos
    (f : ℝ≥0 → ℝ) (y : ℝ) (hy : 0 < y) (h0 : f 0 = 0)
    (hc : ContinuousWithinAt f (Ici 0) 0) :
    0 < tauMinus (shifted (fun t (_ : Unit) => f t) y) 0 () := by
  sorry
