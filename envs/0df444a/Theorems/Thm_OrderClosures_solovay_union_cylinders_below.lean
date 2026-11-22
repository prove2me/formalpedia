-- Prove2me | Theorems.Thm_OrderClosures_solovay_union_cylinders_below
-- name    : OrderClosures.solovay_union_cylinders_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:24.344913+00:00
-- url     : https://prove2.me/theorems/5bf5afc2-50ed-4b99-94ad-49a1cb6f1e67
-- title:
--   Order Closures: solovay union cylinders below
-- statement:
--   Represents the points of a regular open set by cylinders lying below it;
--   used to express that set as a supremum of generated cylinder elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L504-L541
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L504-L541

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

theorem OrderClosures.solovay_union_cylinders_below
    (U : RegularOpen (SolovayProduct Gamma)) :
    (((U : TopologicalSpace.Opens (SolovayProduct Gamma)) :
        Set (SolovayProduct Gamma))) =
      ⋃ V ∈ solovayCylindersBelow Gamma U,
        ((((V : RegularOpen (SolovayProduct Gamma)) :
          TopologicalSpace.Opens (SolovayProduct Gamma)) :
            Set (SolovayProduct Gamma))) := by sorry
