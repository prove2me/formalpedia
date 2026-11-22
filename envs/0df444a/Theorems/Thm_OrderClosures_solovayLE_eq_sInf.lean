-- Prove2me | Theorems.Thm_OrderClosures_solovayLE_eq_sInf
-- name    : OrderClosures.solovayLE_eq_sInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:56.634937+00:00
-- url     : https://prove2.me/theorems/df4a286f-b2b1-4c30-aac7-e3d903e886fc
-- title:
--   Order Closures: solovay LE eq s Inf
-- statement:
--   Expresses a non-strict coordinate bound as an infimum of comparison
--   elements; used in the well-founded generator induction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L365-L411
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L365-L411

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
universe u
variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]

theorem OrderClosures.solovayLE_eq_sInf (n : ℕ) (eta : Gamma) :
    solovayLE Gamma n eta = sInf (Set.range fun m ↦ solovayC Gamma m n eta) := by sorry
