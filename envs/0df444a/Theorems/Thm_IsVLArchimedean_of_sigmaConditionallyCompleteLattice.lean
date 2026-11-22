-- Prove2me | Theorems.Thm_IsVLArchimedean_of_sigmaConditionallyCompleteLattice
-- name    : IsVLArchimedean_of_sigmaConditionallyCompleteLattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:11:42.157809+00:00
-- url     : https://prove2.me/theorems/b5462545-2152-4dab-8a91-1b66c7358343
-- title:
--   Is VLArchimedean of sigma Conditionally Complete Lattice: Is VLArchimedean of sigma Conditionally Complete Lattice
-- statement:
--   Every sigma conditionally complete lattice-ordered group is Archimedean
--   in the vector-lattice sense.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderComplete.lean#L357-L379
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderComplete.lean#L357-L379

module
public import Mathlib.Algebra.Order.Group.Pointwise.Bounds
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Set.Countable
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
set_option autoImplicit true
@[expose] public section
public section
open Set
universe u

theorem IsVLArchimedean_of_sigmaConditionallyCompleteLattice
    {X : Type*} [SigmaConditionallyCompleteLattice X] [AddCommGroup X]
    [IsOrderedAddMonoid X] : IsVLArchimedean X := by sorry
