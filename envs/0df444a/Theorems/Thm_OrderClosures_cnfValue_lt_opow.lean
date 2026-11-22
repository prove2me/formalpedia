-- Prove2me | Theorems.Thm_OrderClosures_cnfValue_lt_opow
-- name    : OrderClosures.cnfValue_lt_opow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:17.709705+00:00
-- url     : https://prove2.me/theorems/113e290a-8936-41be-a4c4-344296b7b70a
-- title:
--   Order Closures: cnf Value lt opow
-- statement:
--   Bounds a valid CNF tail by the next larger omega power; used to compare
--   CNF values after extending a common prefix.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L75-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L75-L94

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

theorem OrderClosures.cnfValue_lt_opow
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hcoeff : ∀ p ∈ l, p.2 < Ordinal.omega0)
    {e : Ordinal.{u}} (hexp : ∀ p ∈ l, p.1 < e) :
    cnfValue l < Ordinal.omega0 ^ e := by sorry
