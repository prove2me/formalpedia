-- Prove2me | Theorems.Thm_OrderClosures_orderAdherence_gaoStage_subset
-- name    : OrderClosures.orderAdherence_gaoStage_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:15.537806+00:00
-- url     : https://prove2.me/theorems/08195f72-1398-4081-bbdb-cbb3f7981161
-- title:
--   Order Closures: order Adherence gao Stage subset
-- statement:
--   Establishes the forward inclusion for one order-adherence step by using a
--   single coordinate dominator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L206-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L206-L215

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.orderAdherence_gaoStage_subset
    (ξ γ : Ordinal.{u}) :
    orderAdherence (GaoStageSet ξ γ) ⊆ GaoStageSet ξ (γ + 1) := by sorry
