-- Prove2me | Theorems.Thm_OrderClosures_orderConvergesTo_gaoProductInclusion
-- name    : OrderClosures.orderConvergesTo_gaoProductInclusion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:49.156794+00:00
-- url     : https://prove2.me/theorems/8f59d7c6-0565-4111-b3c6-053c22583890
-- title:
--   Order Closures: order Converges To gao Product Inclusion
-- statement:
--   Shows that single-coordinate inclusion preserves order convergence; used
--   to lift component adherence witnesses into the global product.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L236-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L236-L303

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

theorem OrderClosures.orderConvergesTo_gaoProductInclusion
    (κ : Cardinal.{u}) (β : GaoComponentIndex κ)
    {i : Type v} [Preorder i] {f : i → GaoComponent β.1}
    {x : GaoComponent β.1} (hfx : OrderConvergesTo f x) :
    OrderConvergesTo (fun j ↦ gaoProductInclusion κ β (f j))
      (gaoProductInclusion κ β x) := by sorry
