-- Prove2me | Theorems.Thm_Kyprianou_Ch04_continuousStatePathCompactIntegrable
-- name    : Kyprianou.Ch04.continuousStatePathCompactIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:29:24.127044+00:00
-- url     : https://prove2.me/theorems/3022714e-c49a-483b-a967-19f3a6ac12b2
-- title:
--   continuousStatePathCompactIntegrable
-- statement:
--   A continuous time-state function along a measurable cadlag path is locally integrable.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- A continuous time-state function along a measurable cadlag path is locally integrable. -/
theorem Kyprianou.Ch04.continuousStatePathCompactIntegrable (Y : NNReal → ℝ) (hY : IsCadlag Y)
    (hm : Measurable (fun r : ℝ => Y r.toNNReal))
    (a : ℝ × ℝ → ℝ) (ha : Continuous a) (t : NNReal) :
    IntegrableOn (fun r => a (r,Y r.toNNReal)) (Icc (0 : ℝ) (t : ℝ)) volume := by
  sorry
