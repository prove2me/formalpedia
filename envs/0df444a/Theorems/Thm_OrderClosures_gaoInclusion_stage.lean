-- Prove2me | Theorems.Thm_OrderClosures_gaoInclusion_stage
-- name    : OrderClosures.gaoInclusion_stage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:06.283876+00:00
-- url     : https://prove2.me/theorems/ae98f495-5e33-4e8f-bbe3-6361c428c6a6
-- title:
--   Order Closures: gao Inclusion stage
-- statement:
--   Propagates component inclusion through every adherence stage; paired with
--   `gaoProjection_stage` to compare the two towers.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L434-L458
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L434-L458

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

theorem OrderClosures.gaoInclusion_stage
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) : ∀ η : Ordinal.{u + 1},
    gaoProductInclusion κ β ''
        (canonicalOrderAdherenceTower (GaoStageSet β.1 1)).stage η ⊆
      (canonicalOrderAdherenceTower (gaoIterationSet κ hκ)).stage η := by sorry
