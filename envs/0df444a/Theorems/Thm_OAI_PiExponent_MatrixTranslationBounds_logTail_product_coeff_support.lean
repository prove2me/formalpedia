-- Prove2me | Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_logTail_product_coeff_support
-- name    : OAI.PiExponent.MatrixTranslationBounds.logTail_product_coeff_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T16:59:55.981184+00:00
-- url     : https://prove2.me/theorems/7da8f9cc-6654-45ff-8788-725687a0a551
-- title:
--   Degree support bound for products of logarithmic tails
-- statement:
--   If every cutoff is at least one, then a nonzero coefficient of a finite product of powers of logarithmic tails can occur only in degree at least the sum of each cutoff multiplied by its exponent. Zero exponents contribute zero, and the empty product has degree zero.
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

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

theorem OAI.PiExponent.MatrixTranslationBounds.logTail_product_coeff_support
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T e : σ → ℕ) (hT : ∀ i, 1 ≤ T i) (k : ℕ) :
    PowerSeries.coeff k
        (∏ i, (tail (T i) (PowerSeries.log ℂ)) ^ (e i)) ≠ 0 →
      (∑ i, T i * e i) ≤ k := by sorry
