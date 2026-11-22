-- Prove2me | Theorems.Thm_OrderClosures_cnfAddMonomial_eq_append_of_lt_all
-- name    : OrderClosures.cnfAddMonomial_eq_append_of_lt_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:54.086275+00:00
-- url     : https://prove2.me/theorems/de0ff1ea-c5d3-4258-be3f-1c96a59351b6
-- title:
--   Order Closures: cnf Add Monomial eq append of lt all
-- statement:
--   Reduces monomial insertion to list append when its exponent is below all
--   existing exponents; used in the strict-extension construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L241-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L241-L250

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Counterexample
public import Mathlib.SetTheory.Ordinal.Principal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.cnfAddMonomial_eq_append_of_lt_all
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d : Ordinal.{u})
    (hγ : ∀ p ∈ l, γ < p.1) :
    cnfAddMonomial l γ d = l ++ [(γ, d)] := by sorry
