-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_product_pow_coeff_ne_zero_degree_bound
-- name    : OAI.PiExponent.LiteralAnalytic.product_pow_coeff_ne_zero_degree_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:44:44.450401+00:00
-- url     : https://prove2.me/theorems/83008595-2341-4e0b-a808-a58bbcb76c00
-- title:
--   Support degree bound for a nonzero coefficient of a product of powers
-- statement:
--   A nonzero coefficient of a product of powers cannot occur below the sum of the coordinate cutoffs multiplied by their exponents. Cutoffs and exponents may be zero.
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

theorem OAI.PiExponent.LiteralAnalytic.product_pow_coeff_ne_zero_degree_bound
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (T d : σ → ℕ) (k : ℕ)
    (hτs : ∀ i n, n < T i → PowerSeries.coeff n (τ i) = 0)
    (hne : PowerSeries.coeff k (∏ i, τ i ^ d i) ≠ 0) :
    ∑ i, T i * d i ≤ k := by sorry
