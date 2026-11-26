-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nonnegativeProbabilityLaplaceUnique
-- name    : Kyprianou.Ch04.nonnegativeProbabilityLaplaceUnique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:21:17.653777+00:00
-- url     : https://prove2.me/theorems/fab1ae06-938d-4241-b845-bf504bc0e213
-- title:
--   Nonnegative probability laws are identified by Laplace transforms
-- statement:
--   Reflect both probability measures onto the negative half-line, apply the proved positive moment-generating-function uniqueness theorem, and reflect back.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.10

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.nonnegativeProbabilityLaplaceUnique (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hm : mu (Iio 0) = 0) (hn : nu (Iio 0) = 0)
    (hEq : ∀ s : ℝ, 0 < s →
      (∫ x, Real.exp (-s*x) ∂mu) = ∫ x, Real.exp (-s*x) ∂nu) :
    mu = nu := by
  sorry
