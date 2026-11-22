-- Prove2me | Theorems.Thm_OrderClosures_solovayVectorGenerators_countable
-- name    : OrderClosures.solovayVectorGenerators_countable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:22.630609+00:00
-- url     : https://prove2.me/theorems/159eb69d-a000-421f-9cea-94bfb70bcab5
-- title:
--   Order Closures: solovay Vector Generators countable
-- statement:
--   Records countability of the selected vector generators; used to prove
--   separability of their closed generated sublattice.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1585-L1587
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1585-L1587

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

theorem OrderClosures.solovayVectorGenerators_countable :
    (solovayVectorGenerators Gamma).Countable := by sorry
