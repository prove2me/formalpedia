-- Prove2me | Theorems.Thm_OrderClosures_orderAdherence_gaoStage
-- name    : OrderClosures.orderAdherence_gaoStage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:13.117818+00:00
-- url     : https://prove2.me/theorems/ca3a581c-8603-42a4-b7aa-2e2e149549bb
-- title:
--   Order Closures: order Adherence gao Stage
-- statement:
--   Packages both inclusions into the one-step Gao-stage formula; used by the
--   transfinite induction in `gao_orderAdherence_stage_formula`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L596-L600
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L596-L600

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.orderAdherence_gaoStage
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    orderAdherence (GaoStageSet ξ γ) = GaoStageSet ξ (γ + 1) := by sorry
