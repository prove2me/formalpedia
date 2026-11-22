-- Prove2me | Theorems.Thm_OrderClosures_solovayVectorSublattice_maximalOrderClosed
-- name    : OrderClosures.solovayVectorSublattice_maximalOrderClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:37.873498+00:00
-- url     : https://prove2.me/theorems/30f57042-f409-46f8-9650-413eab6358a5
-- title:
--   Order Closures: solovay Vector Sublattice maximal Order Closed
-- statement:
--   Shows that every order-closed vector sublattice containing the Solovay
--   sublattice is the whole continuous-function lattice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1626-L1656
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1626-L1656

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
variable (Gamma : Type u) [LinearOrder Gamma] [WellFoundedLT Gamma]
  [TopologicalSpace Gamma] [DiscreteTopology Gamma]

theorem OrderClosures.solovayVectorSublattice_maximalOrderClosed
    (Z : VectorSublattice
      C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ))
    (hYZ : solovayVectorSublattice Gamma ≤ Z)
    (hZorder : IsOrderClosed
      (Z : Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ))) :
    Z = ⊤ := by sorry
