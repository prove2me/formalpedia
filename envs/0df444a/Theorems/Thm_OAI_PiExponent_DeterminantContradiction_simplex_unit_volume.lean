-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_unit_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:54:39.860875+00:00
-- url     : https://prove2.me/theorems/9e2aad48-af7a-492c-b6d1-40ae36fcd9ba
-- title:
--   Unit joint simplex volume
-- statement:
--   The unit simplex in `n+1` nonnegative real coordinates has volume `1/(n+1)!`. This isolates the dimension-dependent integration and factorial calculation.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_unit_volume (n : Nat) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) = ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by sorry
