-- Prove2me | Theorems.Thm_OrderClosures_isSolid_gaoStageSet
-- name    : OrderClosures.isSolid_gaoStageSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:59.801703+00:00
-- url     : https://prove2.me/theorems/7811dc12-2b31-431f-a5f7-7f7d693c5ab9
-- title:
--   Order Closures: is Solid gao Stage Set
-- statement:
--   Records solidity of each Gao stage set; used to invoke the solid form of
--   order adherence in the stage formula.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L82-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L82-L86

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.isSolid_gaoStageSet (ξ β : Ordinal.{u}) :
    LatticeOrderedAddCommGroup.IsSolid (GaoStageSet ξ β) := by sorry
