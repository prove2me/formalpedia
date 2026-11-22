-- Prove2me | Theorems.Thm_OrderConvergesTo_neg
-- name    : OrderConvergesTo.neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:10.253476+00:00
-- url     : https://prove2.me/theorems/f449f644-ce64-4434-b14e-69755e8466ad
-- title:
--   Order Converges To: neg
-- statement:
--   Negation is order continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L245-L260
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L245-L260

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo
omit [IsOrderedAddMonoid X]

theorem OrderConvergesTo.neg {ι : Type v} [Preorder ι]
    {u : ι → X} {x : X} (hu : OrderConvergesTo u x) :
    OrderConvergesTo (fun i => -u i) (-x) := by sorry
