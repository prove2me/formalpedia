-- Prove2me | Theorems.Thm_OrderClosures_solovayVectorGenerator_mem
-- name    : OrderClosures.solovayVectorGenerator_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:22.603833+00:00
-- url     : https://prove2.me/theorems/f9d239b1-59fc-42e6-a549-583314e1f384
-- title:
--   Order Closures: solovay Vector Generator mem
-- statement:
--   Places each selected generator in the Solovay vector sublattice; used to
--   show that any containing sublattice contains the generated Boolean algebra.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1592-L1599
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1592-L1599

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

theorem OrderClosures.solovayVectorGenerator_mem
    {f : C(BooleanStone (RegularOpen (SolovayProduct Gamma)), ℝ)}
    (hf : f ∈ solovayVectorGenerators Gamma) :
    f ∈ solovayVectorSublattice Gamma := by sorry
