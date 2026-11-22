-- Prove2me | Theorems.Thm_OrderClosures_cnfAddMonomial_valid
-- name    : OrderClosures.cnfAddMonomial_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:13.246682+00:00
-- url     : https://prove2.me/theorems/89486506-5107-441f-96a7-a67f576de482
-- title:
--   Order Closures: cnf Add Monomial valid
-- statement:
--   Proves that monomial insertion preserves CNF validity; this allows its
--   value to be recognized by Mathlib's canonical CNF operation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L254-L305
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L254-L305

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

theorem OrderClosures.cnfAddMonomial_valid
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (γ d : Ordinal.{u}) (hdpos : 0 < d) (hdlt : d < Ordinal.omega0) :
    let out := cnfAddMonomial l γ d
    (out.map Prod.fst).Pairwise (fun a b ↦ b < a) ∧
      (∀ p ∈ out, 0 < p.2) ∧
      (∀ p ∈ out, p.2 < Ordinal.omega0) := by sorry
