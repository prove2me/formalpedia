-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyPositiveJumpSumMonotonePointwiseV1
-- name    : Kyprianou.Ch02.bvLevyPositiveJumpSumMonotonePointwiseV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T13:58:38.551232+00:00
-- url     : https://prove2.me/theorems/6c6a9e08-633c-4295-be5a-afe927013dd6
-- title:
--   Positive jump-sum paths are pointwise monotone
-- statement:
--   Fix a real process $X$ and a sample point $\omega$. For times $0\le a\le b$, the cumulative sum of positive jumps of the path $t\mapsto X_t(\omega)$ up to time $a$ does not exceed the corresponding sum up to time $b$. Each summand is nonnegative, and enlarging the time horizon only enlarges the index set of jumps, so the series is monotone in the upper limit.
-- source:
--   Kyprianou Ch.2 Exercise 2.8 / elementary nonnegative series comparison

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyPositiveJumpSumMonotonePointwiseV1
    {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) :
    (∑' s : Set.Ioc (0 : ℝ≥0) a,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0) ≤
      ∑' s : Set.Ioc (0 : ℝ≥0) b,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0 := by sorry
