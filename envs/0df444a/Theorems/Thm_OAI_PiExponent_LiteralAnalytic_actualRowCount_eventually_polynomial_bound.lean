-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actualRowCount_eventually_polynomial_bound
-- name    : OAI.PiExponent.LiteralAnalytic.actualRowCount_eventually_polynomial_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T15:31:44.336766+00:00
-- url     : https://prove2.me/theorems/c6d62ae0-0b77-4601-a990-06e32752eb22
-- title:
--   An eventual polynomial bound for the row count
-- statement:
--   For fixed admissible data, at all sufficiently large cutoffs H the row count is at least one and is bounded above by a fixed positive constant times H to the power d.m + 1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L74-L94

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.LiteralAnalytic.actualRowCount_eventually_polynomial_bound
    {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
      0 < H ∧ 1 ≤ actualRowCount d H ∧
        (actualRowCount d H : ℝ) ≤ C * H ^ (d.m + 1 : ℕ) := by sorry
