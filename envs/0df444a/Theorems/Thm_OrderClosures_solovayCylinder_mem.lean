-- Prove2me | Theorems.Thm_OrderClosures_solovayCylinder_mem
-- name    : OrderClosures.solovayCylinder_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:01.726648+00:00
-- url     : https://prove2.me/theorems/34cd8a78-7bdd-4221-ae86-200bcde14b9c
-- title:
--   Order Closures: solovay Cylinder mem
-- statement:
--   Places every finite Solovay cylinder in a complete subalgebra containing
--   the generators; used to recover arbitrary regular open sets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L472-L488
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L472-L488

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
omit [LinearOrder Gamma]

theorem OrderClosures.solovayCylinder_mem
    (L : BooleanSubalgebra (RegularOpen (SolovayProduct Gamma)))
    (hA : ∀ n eta, solovayA Gamma n eta ∈ L) :
    ∀ F g, solovayCylinder Gamma F g ∈ L := by sorry
