-- Prove2me | Theorems.Thm_OrderConvergesTo_le_of_forall_le
-- name    : OrderConvergesTo.le_of_forall_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:21.201091+00:00
-- url     : https://prove2.me/theorems/addbb932-36f5-4edb-bae6-3f9dfaee3756
-- title:
--   Order Converges To: le of forall le
-- statement:
--   If an order-convergent net is pointwise bounded above, then its limit is bounded above by
--   the same bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L279-L282
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L279-L282

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo

theorem OrderConvergesTo.le_of_forall_le {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x b : X} (hu : OrderConvergesTo u x) (hub : ∀ i, u i ≤ b) :
    x ≤ b := by sorry
