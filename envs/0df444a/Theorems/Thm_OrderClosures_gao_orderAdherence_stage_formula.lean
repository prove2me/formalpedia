-- Prove2me | Theorems.Thm_OrderClosures_gao_orderAdherence_stage_formula
-- name    : OrderClosures.gao_orderAdherence_stage_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:26.706983+00:00
-- url     : https://prove2.me/theorems/f7582e4d-5706-4632-84aa-c5a792d8ceca
-- title:
--   Order Closures: gao order Adherence stage formula
-- statement:
--   Claim 3 in the proof of Theorem `thm:solid-iterations`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L603-L650
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/StageFormula.lean#L603-L650

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gao_orderAdherence_stage_formula
    (ξ : Ordinal.{u}) (T : OrderAdherenceTower (GaoStageSet ξ 1)) :
    ∀ β ≤ ξ, T.stage (Ordinal.lift.{u + 1, u} β) = GaoStageSet ξ (1 + β) := by sorry
