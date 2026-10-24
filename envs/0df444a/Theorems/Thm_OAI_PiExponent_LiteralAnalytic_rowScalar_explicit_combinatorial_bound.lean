-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_explicit_combinatorial_bound
-- name    : OAI.PiExponent.LiteralAnalytic.rowScalar_explicit_combinatorial_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:26:13.588338+00:00
-- url     : https://prove2.me/theorems/4f42bf12-30c7-4151-94a6-f33555641ff1
-- title:
--   Combined binomial and power-series coefficient estimate
-- statement:
--   Bounds the binomial product times the coefficient of the power-series product, using the uniform coefficient bounds and the finite range of each exponent.
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

theorem OAI.PiExponent.LiteralAnalytic.rowScalar_explicit_combinatorial_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (β a : σ →₀ ℕ)
    (e : ∀ i, Fin (a i - β i + 1)) (k : ℕ)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ) *
      ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
        Real.exp (Real.log 4 * (∑ i, (a i : ℝ)) + Real.log 2 * (k : ℝ)) := by sorry
