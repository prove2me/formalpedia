-- Prove2me | Theorems.Thm_OrderClosures_CNFListLT_cnfAddMonomial
-- name    : OrderClosures.CNFListLT_cnfAddMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:39.863807+00:00
-- url     : https://prove2.me/theorems/9d515e8e-7627-46bd-83ac-67cf0e4d1d82
-- title:
--   Order Closures: CNFList LT cnf Add Monomial
-- statement:
--   Shows that adding a sufficiently small monomial gives a strict CNF-list
--   extension; used to approximate ordinals from below.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L341-L404
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L341-L404

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

theorem OrderClosures.CNFListLT_cnfAddMonomial
    (l : List (Ordinal.{u} × Ordinal.{u})) (hne : l ≠ [])
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0)
    (β c : Ordinal.{u}) (hlast : l.getLast? = some (β, c))
    (γ d : Ordinal.{u}) (hdpos : 0 < d)
    (hβγ : β ≤ γ) :
    CNFListLT l (cnfAddMonomial l γ d) := by sorry
