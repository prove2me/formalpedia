-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_of_strict_crossingV1
-- name    : Kyprianou.Ch01.firstUpperPassage_le_of_strict_crossingV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:23:11.439972+00:00
-- url     : https://prove2.me/theorems/e308292f-01f4-496f-bcc9-de049b0d01fc
-- title:
--   A strict upper crossing bounds the first upper-passage time from above
-- statement:
--   For an arbitrary path, any strictly positive time at which the path exceeds a level is an upper bound for its strict first-upper-passage time, including the WithTop representation of nonattainment.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and definition of first strict upper passage.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassage_le_of_strict_crossingV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω)
    (t : ℝ≥0) (ht : 0 < t) (hCross : s < X t ω) :
    firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0) := by
  sorry
