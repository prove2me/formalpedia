-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_rowScalar_binomial_factor_bound
-- name    : OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T17:57:16.557285+00:00
-- url     : https://prove2.me/theorems/5dcaad4c-ecc1-4cd3-a6ed-62951a380ebf
-- title:
--   Weighted majorant for the row binomial factor
-- statement:
--   The complex cast of the natural binomial product has norm at most exp(log(4) weight(w,a)/ws). Each coordinate factor is bounded by 4^(a i), and the positive weight lower bound controls the sum of a i. This includes vanishing binomial coefficients and empty products.
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

theorem OAI.PiExponent.MatrixTranslationBounds.rowScalar_binomial_factor_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ) (ws : ℝ)
    (hws : 0 < ws) (hw : ∀ i, ws ≤ w i) :
    ‖((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : ℂ)‖ ≤
      Real.exp (Real.log 4 * weight w (fun i => a i) / ws) := by sorry
