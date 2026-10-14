-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_exp_weight_difference_of_product_coeff_bound_support_weight
-- name    : OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound_support_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T14:19:58.357769+00:00
-- url     : https://prove2.me/theorems/6e5c971b-f63d-4f73-a0f9-2dd5c307e975
-- title:
--   Cutoff support bounds the weighted exponent sum
-- statement:
--   If the aggregate coefficient is nonzero, the cutoff makes each factor contribute degree at least its cutoff. Together with the bound on k and the cutoff-to-weight inequalities, this bounds the weighted sum of the exponents by H/F.
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

theorem OAI.PiExponent.LiteralAnalytic.rowScalar_exp_weight_difference_of_product_coeff_bound_support_weight
    {s : Type*} [Fintype s] [DecidableEq s]
    (tau : s -> PowerSeries Complex) (beta a : Finsupp s Nat)
    (e : forall i, Fin (a i - beta i + 1)) (k : Nat) (w : s -> Real)
    (H v F : Real) (hv : 0 < v) (hF : 0 < F)
    (hk : (k : Real) <= H / v) (T : s -> Nat)
    (hT : forall i, 1 <= T i)
    (hTw : forall i, F * w i <= v * T i)
    (htaus : forall i n, n < T i -> PowerSeries.coeff n (tau i) = 0)
    (hcoeff : Not (PowerSeries.coeff k (Finset.univ.prod fun i => tau i ^ (e i).val) = 0)) :
    (Finset.univ.sum fun i => w i * (((e i).val : Nat) : Real)) <= H / F := by sorry
