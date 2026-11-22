-- Prove2me | Theorems.Thm_OrderClosures_gaoStage_succ_subset_orderAdherence
-- name    : OrderClosures.gaoStage_succ_subset_orderAdherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:09.190089+00:00
-- url     : https://prove2.me/theorems/f6f8bb9d-bb19-4282-b11a-28fbbab7c526
-- title:
--   Order Closures: gao Stage succ subset order Adherence
-- statement:
--   Establishes the reverse inclusion for a successor Gao stage from the
--   explicit coordinate approximations.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L541-L592
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L541-L592

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoStage_succ_subset_orderAdherence
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    GaoStageSet ξ (γ + 1) ⊆ orderAdherence (GaoStageSet ξ γ) := by sorry
