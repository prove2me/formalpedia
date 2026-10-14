-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_product_coeff_exp_bound_of_coordinate_coeff_bounds
-- name    : OAI.PiExponent.LiteralAnalytic.product_coeff_exp_bound_of_coordinate_coeff_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T13:56:40.085611+00:00
-- url     : https://prove2.me/theorems/10cf2f5e-bf85-451f-8ed4-4dcf453e0115
-- title:
--   Exponential bound for a product coefficient from coordinate coefficient bounds
-- statement:
--   Bounds the requested coefficient by counting degree decompositions across all factors. The strict support assumption is not needed for this estimate; the coefficient-size hypothesis and the weighted degree budget suffice.
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

theorem OAI.PiExponent.LiteralAnalytic.product_coeff_exp_bound_of_coordinate_coeff_bounds
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (a β : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (H ws v : ℝ) (hws : 0 < ws) (hv : 0 < v)
    (hw : ∀ i, ws ≤ w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      Real.exp (H * (Real.log 2 / v + Real.log 4 / ws)) := by sorry
