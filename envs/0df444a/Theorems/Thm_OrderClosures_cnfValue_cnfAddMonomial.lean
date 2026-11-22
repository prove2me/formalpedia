-- Prove2me | Theorems.Thm_OrderClosures_cnfValue_cnfAddMonomial
-- name    : OrderClosures.cnfValue_cnfAddMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:48.525787+00:00
-- url     : https://prove2.me/theorems/11589351-094e-4125-9114-c395a5db73a1
-- title:
--   Order Closures: cnf Value cnf Add Monomial
-- statement:
--   Computes the value after inserting one monomial into a CNF list; used to
--   verify that `cnfAddMonomial` models ordinal addition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L135-L182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L135-L182

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

theorem OrderClosures.cnfValue_cnfAddMonomial
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hd : 0 < d) :
    cnfValue (cnfAddMonomial l γ d) =
      cnfValue l + Ordinal.omega0 ^ γ * d := by sorry
