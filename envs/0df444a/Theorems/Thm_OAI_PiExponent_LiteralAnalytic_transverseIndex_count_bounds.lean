-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_transverseIndex_count_bounds
-- name    : OAI.PiExponent.LiteralAnalytic.transverseIndex_count_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T09:53:20.572037+00:00
-- url     : https://prove2.me/theorems/f4be5f3a-8971-44e5-b583-ea95b739099f
-- title:
--   Box and count bounds for transverse indices and row coordinate
-- statement:
--   The transverse multi-indices lie in a coordinate box of side length ⌊H⌋₊ + 1, their total number is bounded by the size of that box, and the row's first coordinate has at most ⌊H / d.v0⌋₊ + 1 choices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L35-L47

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

theorem OAI.PiExponent.LiteralAnalytic.transverseIndex_count_bounds {nu : ℝ}
    (d : FixedData nu) (H : ℝ) (r : Row d H) :
    Fintype.card (MatrixTranslation.transverseIndices (fixedWeights d) H) ≤
        (⌊H⌋₊ + 1) ^ d.m ∧
      (∀ a ∈ MatrixTranslation.transverseIndices (fixedWeights d) H,
        ∀ i, a i < ⌊H⌋₊ + 1) ∧
      r.2.1 0 + 1 ≤ ⌊H / d.v0⌋₊ + 1 := by
  sorry
