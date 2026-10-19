-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_binomial_factor_bound_nat_majorant
-- name    : OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound_nat_majorant
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:06:22.088664+00:00
-- url     : https://prove2.me/theorems/5d723e87-e360-4775-944b-4af445d20419
-- title:
--   Natural binomial product majorant
-- statement:
--   The complex norm of the natural product of the two binomial coefficients at each coordinate is at most four raised to the sum of the coordinates of a. Each binomial coefficient is bounded by the corresponding power of two; the estimate also covers zero factors and an empty index type.
-- source:
--   OpenAI math repository pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a; lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean, original theorem norm_choiceScalar_le. Pinned platform Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound_nat_majorant
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) :
    ‖((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : ℂ)‖ ≤
      (4 : ℝ) ^ (∑ i, a i) := by sorry
