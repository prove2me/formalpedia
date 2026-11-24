-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyPositiveJumpSumSeriesSummableV1
-- name    : Kyprianou.Ch02.bvLevyPositiveJumpSumSeriesSummableV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:55:41.187192+00:00
-- url     : https://prove2.me/theorems/d5048308-fa05-483c-9f4f-4a1ba6500465
-- title:
--   Positive jump-sum series over an initial interval is summable
-- statement:
--   For every real path $X$, sample $\omega$, and time $t\ge 0$, the series of nonnegative summands $\max(\Delta X_s(\omega),0)$ indexed by $s\in(0,t]$ is summable as a real series.
-- source:
--   Kyprianou (2006), Ch.2, Exercise 2.8 (path regularity obligation)

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyPositiveJumpSumSeriesSummableV1
    {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    Summable fun s : Ioc (0 : ℝ≥0) t =>
      max (X s.1 ω - limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => X u ω)) 0 := by sorry
