-- Prove2me | Theorems.Thm_OrderClosures_isClosed_solovayVectorSublattice
-- name    : OrderClosures.isClosed_solovayVectorSublattice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:26.867806+00:00
-- url     : https://prove2.me/theorems/efda14f9-1bef-478c-9f5a-3eb06c628145
-- title:
--   Order Closures: is Closed solovay Vector Sublattice
-- statement:
--   Records closedness of the generated Solovay vector sublattice; this is one
--   of the properties required by `gao_counterexample`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1604-L1608
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1604-L1608

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

theorem OrderClosures.isClosed_solovayVectorSublattice :
    IsClosed (solovayVectorSublattice Gamma :
      Set C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ)) := by sorry
