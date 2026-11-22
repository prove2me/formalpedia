-- Prove2me | Theorems.Thm_OrderClosures_gaoProjection_initial
-- name    : OrderClosures.gaoProjection_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:12.776184+00:00
-- url     : https://prove2.me/theorems/d0e5b9c4-aa7a-457f-aa6b-fab547463359
-- title:
--   Order Closures: gao Projection initial
-- statement:
--   Proves the initial projection inclusion between the global set and a Gao
--   component; used as the base case of `gaoProjection_stage`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L361-L367
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L361-L367

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

theorem OrderClosures.gaoProjection_initial
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ) :
    gaoProductProjection κ β '' gaoIterationSet κ hκ ⊆ GaoStageSet β.1 1 := by sorry
