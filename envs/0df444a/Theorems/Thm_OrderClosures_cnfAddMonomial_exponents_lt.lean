-- Prove2me | Theorems.Thm_OrderClosures_cnfAddMonomial_exponents_lt
-- name    : OrderClosures.cnfAddMonomial_exponents_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:01.442931+00:00
-- url     : https://prove2.me/theorems/8a847e96-d8d2-43a7-8a68-078621615972
-- title:
--   Order Closures: cnf Add Monomial exponents lt
-- statement:
--   Preserves the upper exponent bound when adding a monomial; needed for the
--   validity proof of the constructed CNF list.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L186-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L186-L207

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

theorem OrderClosures.cnfAddMonomial_exponents_lt
    (l : List (Ordinal.{u} × Ordinal.{u})) (γ d δ : Ordinal.{u})
    (hl : ∀ p ∈ l, p.1 < δ) (hγ : γ < δ) :
    ∀ p ∈ cnfAddMonomial l γ d, p.1 < δ := by sorry
