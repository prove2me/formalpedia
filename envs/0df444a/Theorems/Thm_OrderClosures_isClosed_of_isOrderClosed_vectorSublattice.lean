-- Prove2me | Theorems.Thm_OrderClosures_isClosed_of_isOrderClosed_vectorSublattice
-- name    : OrderClosures.isClosed_of_isOrderClosed_vectorSublattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:58:09.496982+00:00
-- url     : https://prove2.me/theorems/1372a0d9-9b0b-4fb8-96ca-db7ddef2dd5d
-- title:
--   Order Closures: is Closed of is Order Closed vector Sublattice
-- statement:
--   Derives norm closedness of a vector sublattice from order closedness; used
--   to compare the closed separable sublattice with larger order-closed ones.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1413-L1430
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1413-L1430

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u v
variable {K : Type u} [TopologicalSpace K] [CompactSpace K]

theorem OrderClosures.isClosed_of_isOrderClosed_vectorSublattice
    (Z : VectorSublattice C(K, ℝ))
    (hZ : IsOrderClosed (Z : Set C(K, ℝ))) :
    IsClosed (Z : Set C(K, ℝ)) := by sorry
