-- Prove2me | Theorems.Thm_OrderClosures_cnfExtensionLT_iff_CNFListLT
-- name    : OrderClosures.cnfExtensionLT_iff_CNFListLT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:15.060665+00:00
-- url     : https://prove2.me/theorems/a2f057b8-93d7-41fa-8a8c-6968f9c821a5
-- title:
--   Order Closures: cnf Extension LT iff CNFList LT
-- statement:
--   Equates the ordinal definition of `cnfExtensionLT` with its list model;
--   this bridge supplies transitivity and upper-cone linearity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L461-L481
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/CNFOrder.lean#L461-L481

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

theorem OrderClosures.cnfExtensionLT_iff_CNFListLT {ζ ζ' : Ordinal.{u}} :
    cnfExtensionLT ζ ζ' ↔
      CNFListLT (Ordinal.CNF Ordinal.omega0 ζ)
        (Ordinal.CNF Ordinal.omega0 ζ') := by sorry
