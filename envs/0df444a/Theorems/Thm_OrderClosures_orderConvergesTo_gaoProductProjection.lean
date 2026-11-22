-- Prove2me | Theorems.Thm_OrderClosures_orderConvergesTo_gaoProductProjection
-- name    : OrderClosures.orderConvergesTo_gaoProductProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:40.083669+00:00
-- url     : https://prove2.me/theorems/5099f3c7-b4be-4c6f-9d9a-2854d417ef6e
-- title:
--   Order Closures: order Converges To gao Product Projection
-- statement:
--   Shows that coordinate projection preserves order convergence; used to
--   project every global adherence stage to its component stage.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L197-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L197-L232

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

theorem OrderClosures.orderConvergesTo_gaoProductProjection
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ)
    {i : Type v} [Preorder i] {f : i → GaoIterationProduct κ}
    {x : GaoIterationProduct κ} (hfx : OrderConvergesTo f x) :
    OrderConvergesTo (fun j ↦ gaoProductProjection κ β (f j))
      (gaoProductProjection κ β x) := by sorry
