-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_weight_difference_of_product_coeff_bound
-- name    : OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T13:55:51.318154+00:00
-- url     : https://prove2.me/theorems/7679f8df-3541-4d60-821c-ceb138b79b4e
-- title:
--   Weighted row scalar bound from an aggregate product coefficient estimate
-- statement:
--   Converts an aggregate coefficient bound into the rowScalar estimate. The cutoff support, together with hTw and hk, bounds the weighted total exponent of the τ powers by H/F, which supplies the ν/F term while the ε and binomial factors supply the remaining terms.
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

theorem OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (τ : σ → PowerSeries ℂ) (β a : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (T : σ → ℕ)
    (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hτs : ∀ i n, n < T i → PowerSeries.coeff n (τ i) = 0)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i))
    (hprod : ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      Real.exp (H * (Real.log 2 / v + Real.log 4 / ws))) :
    ‖RowTranslation.rowScalar ε τ β a e k‖ ≤
      Real.exp (-ν * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by sorry
