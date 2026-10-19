-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_binomial_factor_bound_weight_exp
-- name    : OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound_weight_exp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:06:53.412857+00:00
-- url     : https://prove2.me/theorems/26409af8-de12-4e45-b8a5-1fe0ea9d2142
-- title:
--   Weighted sum exponential comparison
-- statement:
--   For positive ws bounded above by every weight, the fourth power indexed by the sum of the natural coordinates of a is at most the exponential of log 4 times the weighted sum divided by ws. This includes the empty sum.
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

theorem OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound_weight_exp
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a : σ →₀ ℕ) (w : σ → ℝ) (ws : ℝ)
    (hws : 0 < ws) (hw : ∀ i, ws ≤ w i) :
    (4 : ℝ) ^ (∑ i, a i) ≤
      Real.exp (Real.log 4 * weight w (fun i => a i) / ws) := by sorry
