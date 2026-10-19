-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_actual_error_exp
-- name    : OAI.PiExponent.MatrixTranslationBounds.actual_error_exp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:23:52.863759+00:00
-- url     : https://prove2.me/theorems/d2d00131-7cd7-4366-8214-41e493fc3b14
-- title:
--   Exponential estimate for the rational-center error
-- statement:
--   For positive natural denominators and a nonnegative approximation exponent, bound each scaled rational-center error by the exponential determined by its rounded logarithmic weight.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

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
import Definitions.Def_OAI_PiExponent_LiteralAnalytic_choiceScalarMajorant

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixArithmetic

theorem OAI.PiExponent.MatrixTranslationBounds.actual_error_exp {m : ℕ}
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (j K : ℕ) (ν : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hν : 0 ≤ ν)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |Real.pi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-ν)) :
    ∀ i, ‖(j : ℂ) * (MatrixArithmetic.rationalCenters p q i - logarithmicPeriod)‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + ν) -
        ν * MatrixArithmetic.logWeights q i) := by sorry
