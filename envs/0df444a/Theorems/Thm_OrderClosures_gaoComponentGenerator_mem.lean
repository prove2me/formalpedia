-- Prove2me | Theorems.Thm_OrderClosures_gaoComponentGenerator_mem
-- name    : OrderClosures.gaoComponentGenerator_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:54.185791+00:00
-- url     : https://prove2.me/theorems/38607d1a-7ef6-4e75-8f89-e74830603e09
-- title:
--   Order Closures: gao Component Generator mem
-- statement:
--   Places each embedded component generator in the global solid generator
--   set; this initializes the stage-inclusion induction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L333-L357
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L333-L357

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

theorem OrderClosures.gaoComponentGenerator_mem
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (β : GaoComponentIndex κ)
    (a : ULift.{u + 1, u} (Cardinal.ord κ).ToType) :
    gaoComponentGenerator κ hκ β a ∈ GaoStageSet β.1 1 := by sorry
