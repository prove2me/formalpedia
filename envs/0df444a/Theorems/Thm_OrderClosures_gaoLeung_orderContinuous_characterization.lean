-- Prove2me | Theorems.Thm_OrderClosures_gaoLeung_orderContinuous_characterization
-- name    : OrderClosures.gaoLeung_orderContinuous_characterization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:24.280011+00:00
-- url     : https://prove2.me/theorems/c4d37ade-0d1a-4d6d-9f60-b1ea5ae00df7
-- title:
--   Order Closures: gao Leung order Continuous characterization
-- statement:
--   Gao--Leung, Theorem 2.7 (paper Theorem `ND`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungCharacterization.lean#L1012-L1036
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungCharacterization.lean#L1012-L1036

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungCharacterization
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped BoundedContinuousFunction
universe u
variable {X : Type u} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X]

theorem OrderClosures.gaoLeung_orderContinuous_characterization :
    ((∀ Y : VectorSublattice X, IsOrderClosed (orderAdherence (Y : Set X))) ↔
      (∀ Y : VectorSublattice X, orderAdherence (Y : Set X) = uoAdherence (Y : Set X))) ∧
    ((∀ Y : VectorSublattice X, orderAdherence (Y : Set X) = uoAdherence (Y : Set X)) ↔
      IsOrderContinuousNorm X) := by sorry
