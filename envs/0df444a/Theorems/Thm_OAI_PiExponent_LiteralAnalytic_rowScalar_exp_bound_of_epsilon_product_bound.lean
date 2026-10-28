-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_bound_of_epsilon_product_bound
-- name    : OAI.PiExponent.LiteralAnalytic.rowScalar_exp_bound_of_epsilon_product_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:32:14.537112+00:00
-- url     : https://prove2.me/theorems/aad96d4e-f5b4-4402-8339-6247f87c8e3d
-- title:
--   Assemble the row scalar estimate from product bounds
-- statement:
--   Combines a bound on the epsilon product with the supplied combined coefficient estimate to bound the row scalar.
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

theorem OAI.PiExponent.LiteralAnalytic.rowScalar_exp_bound_of_epsilon_product_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (τ : σ → PowerSeries ℂ) (β a : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν : ℝ)
    (hEpsProd :
      ‖∏ i, ε i ^ (a i - β i - (e i : ℕ))‖ ≤
        Real.exp (C * (∑ i, (a i : ℝ)) - ν *
          (MatrixTranslationBounds.weight w (fun i => a i) -
            MatrixTranslationBounds.weight w (fun i => β i)) +
          ν * MatrixTranslationBounds.weight w (fun i => (e i : ℕ))))
    (hComb :
      ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ) *
        ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
          Real.exp (Real.log 4 * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ))) :
    ‖RowTranslation.rowScalar ε τ β a e k‖ ≤
      Real.exp (-ν * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => β i)) +
        ν * MatrixTranslationBounds.weight w (fun i => (e i : ℕ)) +
        (Real.log 4 + C) * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ)) := by sorry
