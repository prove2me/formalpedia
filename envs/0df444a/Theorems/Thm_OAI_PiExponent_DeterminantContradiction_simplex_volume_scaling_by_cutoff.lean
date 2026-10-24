-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_scaling_by_cutoff
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_volume_scaling_by_cutoff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:20:37.553104+00:00
-- url     : https://prove2.me/theorems/89322c7d-f3a1-415f-bd26-3b1929dc9039
-- title:
--   Scaling the joint simplex by its cutoff
-- statement:
--   For positive `T`, scaling every coordinate of the unit simplex by `T` multiplies its volume by `T^(n+1)`. This isolates the diagonal change-of-variables step.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_volume_scaling_by_cutoff (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n T) = ENNReal.ofReal (T ^ (n + 1)) * MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) := by sorry
