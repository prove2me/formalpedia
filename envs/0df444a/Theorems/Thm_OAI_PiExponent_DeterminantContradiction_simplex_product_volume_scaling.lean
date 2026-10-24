-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_product_volume_scaling
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_product_volume_scaling
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:54:22.812992+00:00
-- url     : https://prove2.me/theorems/ca28342b-39b9-4f66-8eb2-125c5e1cd8d0
-- title:
--   Scaling the joint simplex
-- statement:
--   Scaling every coordinate of the unit simplex by positive `T` multiplies its volume by `T^(n+1)`. This isolates the diagonal change-of-variables step and its determinant factor.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_product_volume_scaling (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n T) = ENNReal.ofReal (T ^ (n + 1)) * MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) := by sorry
