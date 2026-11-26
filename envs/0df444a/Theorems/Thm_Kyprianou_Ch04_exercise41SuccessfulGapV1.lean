-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulGapV1
-- name    : Kyprianou.Ch04.exercise41SuccessfulGapV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:42:53.534501+00:00
-- url     : https://prove2.me/theorems/3dcf29fd-1ebe-4a15-b5bd-4e1903452ea3
-- title:
--   Positive slope separates near-zero sampled values
-- statement:
--   If two real values have absolute value less than d*h/8, their difference cannot dominate d*dt/2 for dt at least h.
-- source:
--   Kyprianou (2006), Exercise 4.1(i)–(ii), printed pp.105–106.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_smallTimeDriftLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise41SuccessfulGapV1
    (d h x y dt : ℝ) (hd : 0 < d) (hh : 0 < h)
    (hx : |x| < d * h / 8) (hy : |y| < d * h / 8)
    (hslope : d / 2 * dt ≤ y - x) : dt < h := by
  sorry
