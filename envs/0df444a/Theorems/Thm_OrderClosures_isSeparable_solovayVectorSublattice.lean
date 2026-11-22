-- Prove2me | Theorems.Thm_OrderClosures_isSeparable_solovayVectorSublattice
-- name    : OrderClosures.isSeparable_solovayVectorSublattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:42.072801+00:00
-- url     : https://prove2.me/theorems/2c3f0ef5-5d34-4f8a-b209-990ad9c8f7a3
-- title:
--   Order Closures: is Separable solovay Vector Sublattice
-- statement:
--   Derives separability from the countable generator family; this supplies
--   the separable sublattice in `gao_counterexample`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1613-L1622
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1613-L1622

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
omit [WellFoundedLT Gamma]

theorem OrderClosures.isSeparable_solovayVectorSublattice :
    TopologicalSpace.IsSeparable (solovayVectorSublattice Gamma :
      Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ)) := by sorry
