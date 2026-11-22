-- Prove2me | Theorems.Thm_OrderClosures_cnfExtensionLT_linear_above
-- name    : OrderClosures.cnfExtensionLT_linear_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:14.551617+00:00
-- url     : https://prove2.me/theorems/d37bbc19-3224-4819-b810-4633918f9d38
-- title:
--   Order Closures: cnf Extension LT linear above
-- statement:
--   Property P2 of the ordinal relation in the proof of `thm:solid-iterations`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L701-L717
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L701-L717

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

theorem OrderClosures.cnfExtensionLT_linear_above (ζ : Ordinal.{u}) :
    ∀ {η η' : Ordinal.{u}}, cnfExtensionLT ζ η → cnfExtensionLT ζ η' →
      (cnfExtensionLT η η' ↔ η < η') := by sorry
