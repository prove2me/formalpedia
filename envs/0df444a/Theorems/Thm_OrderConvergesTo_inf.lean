-- Prove2me | Theorems.Thm_OrderConvergesTo_inf
-- name    : OrderConvergesTo.inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:17.165187+00:00
-- url     : https://prove2.me/theorems/a3da9ddc-d3a0-4db7-a955-e98c58b6d12f
-- title:
--   Order Converges To: inf
-- statement:
--   Infimum is order continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L347-L351
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L347-L351

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo

theorem OrderConvergesTo.inf {ι : Type v} [Preorder ι]
    {u v : ι → X} {x y : X} (hu : OrderConvergesTo u x)
    (hv : OrderConvergesTo v y) :
    OrderConvergesTo (fun i => u i ⊓ v i) (x ⊓ y) := by sorry
