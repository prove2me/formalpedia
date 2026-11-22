-- Prove2me | Theorems.Thm_OrderConvergesTo_sub
-- name    : OrderConvergesTo.sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:11.762376+00:00
-- url     : https://prove2.me/theorems/349ddf00-c958-4ee2-9a77-9cddbf905559
-- title:
--   Order Converges To: sub
-- statement:
--   Subtraction is order continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L263-L267
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L263-L267

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo

theorem OrderConvergesTo.sub {ι : Type v} [Preorder ι]
    {u v : ι → X} {x y : X} (hu : OrderConvergesTo u x)
    (hv : OrderConvergesTo v y) :
    OrderConvergesTo (fun i => u i - v i) (x - y) := by sorry
