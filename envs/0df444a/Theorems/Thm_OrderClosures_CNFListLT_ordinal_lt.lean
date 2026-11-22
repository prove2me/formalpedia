-- Prove2me | Theorems.Thm_OrderClosures_CNFListLT_ordinal_lt
-- name    : OrderClosures.CNFListLT.ordinal_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:10.542387+00:00
-- url     : https://prove2.me/theorems/f3fe1182-f62d-4460-bd37-b24cc3c8b4a4
-- title:
--   CNFList LT: ordinal lt
-- statement:
--   Converts strict extension of canonical CNF lists into strict ordinal
--   inequality; used throughout the ordinal-space construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L420-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L420-L457

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

theorem OrderClosures.CNFListLT.ordinal_lt {ζ ζ' : Ordinal.{u}}
    (h : CNFListLT (Ordinal.CNF Ordinal.omega0 ζ)
      (Ordinal.CNF Ordinal.omega0 ζ')) : ζ < ζ' := by sorry
