-- Prove2me | Theorems.Thm_OrderClosures_solovayCylinder_insert
-- name    : OrderClosures.solovayCylinder_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:13.857796+00:00
-- url     : https://prove2.me/theorems/b6e7d046-96df-48c8-8ada-556ddde4c293
-- title:
--   Order Closures: solovay Cylinder insert
-- statement:
--   Splits a finite cylinder after inserting one coordinate; used for the
--   induction showing all finite cylinders are generated.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L459-L467
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L459-L467

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

theorem OrderClosures.solovayCylinder_insert (i : ℕ) (F : Finset ℕ)
    (g : SolovayProduct Gamma) :
    solovayCylinder Gamma (insert i F) g =
      solovayA Gamma i (g i) ⊓ solovayCylinder Gamma F g := by sorry
