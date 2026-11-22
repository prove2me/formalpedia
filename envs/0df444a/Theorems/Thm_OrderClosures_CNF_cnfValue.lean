-- Prove2me | Theorems.Thm_OrderClosures_CNF_cnfValue
-- name    : OrderClosures.CNF_cnfValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:08.047545+00:00
-- url     : https://prove2.me/theorems/363c1585-3490-437d-a1bf-727880942de2
-- title:
--   Order Closures: CNF cnf Value
-- statement:
--   Shows that evaluating the CNF list of an ordinal recovers that ordinal;
--   used to translate between list and ordinal formulations of the extension order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L98-L120
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L98-L120

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

theorem OrderClosures.CNF_cnfValue
    (l : List (Ordinal.{u} × Ordinal.{u}))
    (hsorted : (l.map Prod.fst).Pairwise (fun a b ↦ b < a))
    (hpos : ∀ p ∈ l, 0 < p.2)
    (hlt : ∀ p ∈ l, p.2 < Ordinal.omega0) :
    Ordinal.CNF Ordinal.omega0 (cnfValue l) = l := by sorry
