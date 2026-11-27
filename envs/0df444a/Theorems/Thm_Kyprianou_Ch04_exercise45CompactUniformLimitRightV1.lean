-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45CompactUniformLimitRightV1
-- name    : Kyprianou.Ch04.exercise45CompactUniformLimitRightV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:36:06.980176+00:00
-- url     : https://prove2.me/theorems/e8bb3eda-6313-4f8e-bb4a-fa9ec74c30de
-- title:
--   A compact uniform limit of right-continuous paths is right-continuous
-- statement:
--   Choose a single approximating path within a quarter of the desired accuracy on the compact horizon and use its right continuity at the interior time.
-- source:
--   Kyprianou (2006), Exercise 4.5 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45CompactUniformLimitRightV1
    (A : ℕ → NNReal → ℝ) (Z : NNReal → ℝ)
    (T t : NNReal) (ht : t < T)
    (hR : ∀ n : ℕ, ContinuousWithinAt (A n) (Ici t) t)
    (hU : ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ s ≤ T, |A n s - Z s| ≤ δ) :
    ContinuousWithinAt Z (Ici t) t := by sorry
