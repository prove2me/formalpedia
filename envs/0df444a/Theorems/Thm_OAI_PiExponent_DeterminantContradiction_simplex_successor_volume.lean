-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_successor_volume
-- name    : OAI.PiExponent.DeterminantContradiction.simplex_successor_volume
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:28:47.714467+00:00
-- url     : https://prove2.me/theorems/1bcd4117-64fd-4aab-8bde-d606e25ad321
-- title:
--   Simplex volume successor recurrence
-- statement:
--   Adding one coordinate changes the unit simplex volume by the factor 1/(n+2). Slicing by the added coordinate gives lower-dimensional simplices of size 1−x, whose volumes scale as (1−x)^(n+1); integrating these sections gives the recurrence.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_simplexRegion

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.simplex_successor_volume (n : Nat) : MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion (n + 1) 1) = ENNReal.ofReal (1 / (n + 2 : Real)) * MeasureTheory.volume (OAI.PiExponent.DeterminantContradiction.simplexRegion n 1) := by sorry
