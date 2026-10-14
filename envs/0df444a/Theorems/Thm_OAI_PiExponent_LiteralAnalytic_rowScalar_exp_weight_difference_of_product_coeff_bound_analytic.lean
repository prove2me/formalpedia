-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_weight_difference_of_product_coeff_bound_analytic
-- name    : OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound_analytic
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T14:20:26.574661+00:00
-- url     : https://prove2.me/theorems/342f536e-0afb-49a0-9b74-f393f9a30e67
-- title:
--   Weighted row scalar estimate from an exponent sum and aggregate coefficient bound
-- statement:
--   Given the weighted exponent-sum bound, the aggregate coefficient estimate and the coordinate bounds on eps imply the requested rowScalar estimate. The condition e_i ≤ a_i - beta_i supplies the binomial and epsilon powers used in the estimate.
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

theorem OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound_analytic
    {s : Type*} [Fintype s] [DecidableEq s]
    (eps : s -> Complex) (tau : s -> PowerSeries Complex) (beta a : Finsupp s Nat)
    (e : forall i, Fin (a i - beta i + 1)) (k : Nat) (w : s -> Real)
    (C nu H ws v F : Real) (hC : 0 <= C) (hnu : 0 <= nu)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : forall i, ws <= w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) <= H)
    (hd : (Finset.univ.sum fun i => w i * (((e i).val : Nat) : Real)) <= H / F)
    (heps : forall i, ‖eps i‖ <= Real.exp (C - nu * w i))
    (hprod : ‖PowerSeries.coeff k (Finset.univ.prod fun i => tau i ^ (e i).val)‖ <=
      Real.exp (H * (Real.log 2 / v + Real.log 4 / ws))) :
    ‖RowTranslation.rowScalar eps tau beta a e k‖ <=
      Real.exp (-nu * (MatrixTranslationBounds.weight w (fun i => a i) -
        MatrixTranslationBounds.weight w (fun i => beta i)) +
        H * (nu / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by sorry
