-- Prove2me | Theorems.Thm_OrderClosures_regularOpen_eq_sSup_of_union
-- name    : OrderClosures.regularOpen_eq_sSup_of_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:33.487181+00:00
-- url     : https://prove2.me/theorems/77698c76-f5b4-4cb7-8484-08c30f391ce3
-- title:
--   Order Closures: regular Open eq s Sup of union
-- statement:
--   Recovers a regular open set as the supremum of a family whose union is
--   dense in it; used in the proof that the Solovay generators are complete.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L155-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L155-L179

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

theorem OrderClosures.regularOpen_eq_sSup_of_union {X : Type u} [TopologicalSpace X]
    (U : RegularOpen X) (S : Set (RegularOpen X))
    (hunion : (((U : TopologicalSpace.Opens X) : Set X)) = ⋃ V ∈ S,
      ((((V : RegularOpen X) : TopologicalSpace.Opens X) : Set X))) :
    U = sSup S := by sorry
