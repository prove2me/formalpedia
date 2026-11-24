-- Prove2me | Theorems.Thm_Kyprianou_Ch02_monotoneClockLeLeftLimitV1
-- name    : Kyprianou.Ch02.monotoneClockLeLeftLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:47:42.659777+00:00
-- url     : https://prove2.me/theorems/765c8218-b547-46c4-8d9b-62138e77343f
-- title:
--   A monotone clock before a time is bounded by its left limit
-- statement:
--   A monotone nonnegative clock is bounded by its left limit at every earlier time.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.monotoneClockLeLeftLimitV1
    (g : ℝ≥0 → ℝ≥0) (hm : Monotone g) (t u : ℝ≥0)
    (hu : Tendsto g (nhdsWithin t (Set.Iio t)) (nhds u))
    (r : ℝ≥0) (hr : r < t) : g r ≤ u := by sorry
