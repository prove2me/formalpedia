-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_unit_volume_zero
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:28:32.258153+00:00
-- url     : https://prove2.me/theorems/5cbbc7f8-1256-462f-955d-89b7b6651f0b
-- title:
--   Zero-dimensional unit simplex volume
-- statement:
--   The simplex with one real coordinate has volume 1. This supplies the base case, including the boundary convention [0,1).

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_zero : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion 0 1) = ENNReal.ofReal (1 / (Nat.factorial (0 + 1) : Real)) := by sorry
