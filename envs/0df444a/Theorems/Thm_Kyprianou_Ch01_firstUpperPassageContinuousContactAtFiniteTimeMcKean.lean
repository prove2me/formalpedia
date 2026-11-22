-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassageContinuousContactAtFiniteTimeMcKean
-- name    : Kyprianou.Ch01.firstUpperPassageContinuousContactAtFiniteTimeMcKean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T15:19:11.554064+00:00
-- url     : https://prove2.me/theorems/8b03bd1b-ad61-495a-be64-e33606e08f6d
-- title:
--   Continuous first upper passage hits its barrier at every finite stopping time
-- statement:
--   For a continuous path starting at zero, the first strict passage above a positive level, when finite, has the level itself as its path value. This contact identity is the pathwise step needed to replace a stopped perpetual put payoff with its discounted first-passage Laplace factor. Reuse the proved continuousUpperPassageDiscountedExpLimitPublic if useful.
-- source:
--   Kyprianou (2006), Chapter 1, McKean theorem, continuity of Brownian paths at hitting times.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassageContinuousContactAtFiniteTimeMcKean
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (s : ℝ) (hs : 0 < s)
    (hContinuous : Continuous (fun t : ℝ≥0 => Y t ω))
    (hStart : Y 0 ω = 0)
    (t : ℝ≥0)
    (hPass : firstUpperPassage Y s ω = (t : WithTop ℝ≥0)) :
    Y t ω = s := by sorry
