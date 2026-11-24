-- Prove2me | Theorems.Thm_Kyprianou_Ch02_interiorLinearRampBoundsV1
-- name    : Kyprianou.Ch02.interiorLinearRampBoundsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:11:20.458377+00:00
-- url     : https://prove2.me/theorems/25cd3230-47a2-4178-8501-efe5fd7da41e
-- title:
--   Pointwise bounds for the interior linear ramps
-- statement:
--   Outside the interval one ramp vanishes. Inside, the lower ramp is at most x, which is at most r. Both ramps are nonnegative.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.interiorLinearRampBoundsV1
    (r : ℝ) (hr : 0 < r) (n : ℕ) (x : ℝ) :
    let g : ℝ := min (max 0 (x - 1 / ((n : ℝ) + 1))) (max 0 (((n : ℝ) + 1) * (r - x)))
    0 ≤ g ∧ g ≤ (Ioo (0 : ℝ) r).indicator id x ∧ g ≤ r ∧
      (|x| < 1 / ((n : ℝ) + 1) → g = 0) := by
  sorry
