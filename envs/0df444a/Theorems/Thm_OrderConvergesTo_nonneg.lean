-- Prove2me | Theorems.Thm_OrderConvergesTo_nonneg
-- name    : OrderConvergesTo.nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:03.658927+00:00
-- url     : https://prove2.me/theorems/6f6375e1-9ace-475c-89a5-cc361d6e9204
-- title:
--   Order Converges To: nonneg
-- statement:
--   The positive cone is order closed: a pointwise non-negative order-convergent net has a
--   non-negative limit.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L199-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L199-L212

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo

theorem OrderConvergesTo.nonneg {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {u : ι → X} {x : X} (hu : OrderConvergesTo u x) (hnn : ∀ i, 0 ≤ u i) :
    0 ≤ x := by sorry
