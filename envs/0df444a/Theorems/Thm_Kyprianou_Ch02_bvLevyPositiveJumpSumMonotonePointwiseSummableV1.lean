-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyPositiveJumpSumMonotonePointwiseSummableV1
-- name    : Kyprianou.Ch02.bvLevyPositiveJumpSumMonotonePointwiseSummableV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:55:38.143998+00:00
-- url     : https://prove2.me/theorems/e27c5c55-0cd5-477a-a718-20319f65a983
-- title:
--   Summable positive jump sums are monotone in the time horizon
-- statement:
--   Let $X$ be a real path and fix a sample $\omega$. Write $J(t)$ for the sum of positive jumps of $X(\cdot,\omega)$ over $(0,t]$. If the series defining $J(a)$ and $J(b)$ are summable and $a\le b$, then $J(a)\le J(b)$.
-- source:
--   Kyprianou (2006), Ch.2, Exercise 2.8 (summable correction)

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyPositiveJumpSumMonotonePointwiseSummableV1
    {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hf : Summable fun s : Ioc (0 : ℝ≥0) a =>
      max (X s.1 ω - limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => X u ω)) 0)
    (hg : Summable fun s : Ioc (0 : ℝ≥0) b =>
      max (X s.1 ω - limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => X u ω)) 0) :
    (∑' s : Ioc (0 : ℝ≥0) a,
        max (X s.1 ω -
          limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => X u ω)) 0) ≤
      ∑' s : Ioc (0 : ℝ≥0) b,
        max (X s.1 ω -
          limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => X u ω)) 0 := by sorry
