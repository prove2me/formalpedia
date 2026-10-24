-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_by_dimension
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_by_dimension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:20:55.503878+00:00
-- url     : https://prove2.me/theorems/4438821d-a44d-4adc-ac3f-9bfe14df1a99
-- title:
--   Unit joint simplex volume by dimension
-- statement:
--   The unit simplex in `n+1` nonnegative real coordinates has volume `1/(n+1)!`. This isolates the dimension induction and slicing integral.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_by_dimension (n : Nat) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) = ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by sorry
