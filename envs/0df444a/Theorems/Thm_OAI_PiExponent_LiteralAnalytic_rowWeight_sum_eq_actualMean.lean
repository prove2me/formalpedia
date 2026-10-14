-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowWeight_sum_eq_actualMean
-- name    : OAI.PiExponent.LiteralAnalytic.rowWeight_sum_eq_actualMean
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T12:51:35.347565+00:00
-- url     : https://prove2.me/theorems/4c6eb0c8-c7aa-447e-82b4-77e6a38d5850
-- title:
--   Row weights sum to the actual mean budget
-- statement:
--   The sum of the row weights over all rows equals the row count times the height times the defined actual mean. This converts the summed rowwise exponent into the target exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L163-L175

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.LiteralAnalytic.rowWeight_sum_eq_actualMean
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (∑ r : Row d H, rowWeight d r) =
      (actualRowCount d H : ℝ) * H * actualMean d H := by sorry
