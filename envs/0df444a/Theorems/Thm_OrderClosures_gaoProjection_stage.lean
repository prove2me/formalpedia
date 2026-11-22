-- Prove2me | Theorems.Thm_OrderClosures_gaoProjection_stage
-- name    : OrderClosures.gaoProjection_stage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:05.633905+00:00
-- url     : https://prove2.me/theorems/8c9bd0d2-86df-498d-bc2b-77ea135e2620
-- title:
--   Order Closures: gao Projection stage
-- statement:
--   Propagates the projection inclusion through every adherence stage; used
--   to transfer component strictness to the global tower.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L406-L430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L406-L430

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.gaoProjection_stage
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) : ∀ η : Ordinal.{u + 1},
    gaoProductProjection κ β ''
        (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage η ⊆
      (canonicalOrderAdherenceTower (GaoStageSet β.1 1)).stage η := by sorry
