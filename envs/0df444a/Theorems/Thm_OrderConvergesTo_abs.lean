-- Prove2me | Theorems.Thm_OrderConvergesTo_abs
-- name    : OrderConvergesTo.abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:10.717571+00:00
-- url     : https://prove2.me/theorems/388b7ad8-42b7-42c0-92ed-af340581de79
-- title:
--   Order Converges To: abs
-- statement:
--   Absolute value is order continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L354-L358
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L354-L358

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo

theorem OrderConvergesTo.abs {ι : Type v} [Preorder ι]
    {u : ι → X} {x : X} (hu : OrderConvergesTo u x) :
    OrderConvergesTo (fun i => |u i|) |x| := by sorry
