-- Prove2me | Theorems.Thm_OrderConvergesTo_smul
-- name    : OrderConvergesTo.smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:03.826274+00:00
-- url     : https://prove2.me/theorems/853dcfc7-72fd-41fb-9b7d-25bbfa49207b
-- title:
--   Order Converges To: smul
-- statement:
--   Scalar multiplication is order continuous.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L292-L320
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Convergences/Order.lean#L292-L320

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
set_option autoImplicit true
@[expose] public section
public section
universe u v
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
open OrderConvergesTo

theorem OrderConvergesTo.smul [VectorLattice X] (a : ℝ) {ι : Type v} [Preorder ι]
      {u : ι → X} {x : X}
    (hu : OrderConvergesTo u x) :
    OrderConvergesTo (fun i => a • u i) (a • x) := by sorry
