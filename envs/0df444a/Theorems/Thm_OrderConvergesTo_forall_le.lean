-- Prove2me | Theorems.Thm_OrderConvergesTo_forall_le
-- name    : OrderConvergesTo.forall_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:38.59668+00:00
-- url     : https://prove2.me/theorems/b41da853-d112-4417-b028-4faec159efe4
-- title:
--   Order Converges To: forall le
-- statement:
--   If an order-convergent net is pointwise bounded below, then its limit is bounded below by
--   the same bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L286-L289
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L286-L289

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo

theorem OrderConvergesTo.forall_le {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {a x : X} (hu : OrderConvergesTo u x) (hau : ∀ i, a ≤ u i) :
    a ≤ x := by sorry
