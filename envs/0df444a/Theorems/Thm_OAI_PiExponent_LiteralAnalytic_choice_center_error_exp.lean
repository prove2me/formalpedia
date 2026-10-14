-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choice_center_error_exp
-- name    : OAI.PiExponent.LiteralAnalytic.choice_center_error_exp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T13:02:54.80071+00:00
-- url     : https://prove2.me/theorems/a7e1ab45-f43c-4d80-b17b-e347b232be20
-- title:
--   Exponential estimate for each rational-center error
-- statement:
--   Converts the rational approximation bounds in `FixedData` into the pointwise exponential bound needed by the weighted scalar estimate. It retains the nonnegative exponent hypothesis and the index bound `j ≤ d.K`.
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

theorem OAI.PiExponent.LiteralAnalytic.choice_center_error_exp
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    (j : ℕ) (hj : j ≤ d.K) (i : Fin d.m) :
    ‖(j : ℂ) * (MatrixArithmetic.rationalCenters (finiteNumerators d)
      (finiteDenominators d) i - logarithmicPeriod)‖ ≤
      Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i) := by sorry
