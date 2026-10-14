-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choice_scalar_weight_inputs
-- name    : OAI.PiExponent.LiteralAnalytic.choice_scalar_weight_inputs
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T13:03:25.781498+00:00
-- url     : https://prove2.me/theorems/b7b18de2-22fb-4fbe-887c-a1193a10a979
-- title:
--   Row-choice weight and truncation budgets
-- statement:
--   Collects the positive parameter bounds and row-choice weight, coefficient-index, and truncation budgets needed by the weighted scalar estimate. Positive height is required for the row and choice index bounds.
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

theorem OAI.PiExponent.LiteralAnalytic.choice_scalar_weight_inputs
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) (t : RowChoice d H r) :
    0 < d.wstar ∧ 0 < (d.v0 : ℝ) ∧ 0 < d.F0 ∧
    (∀ i, d.wstar ≤ fixedWeights d i) ∧
    MatrixTranslationBounds.weight (fixedWeights d) (fun i => t.1.1 i) ≤ H ∧
    (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ) ∧
    (∀ i, 1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) ∧
    (∀ i, d.F0 * fixedWeights d i ≤ (d.v0 : ℝ) *
      MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) := by sorry
