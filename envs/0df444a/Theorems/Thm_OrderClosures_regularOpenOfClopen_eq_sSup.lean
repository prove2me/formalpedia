-- Prove2me | Theorems.Thm_OrderClosures_regularOpenOfClopen_eq_sSup
-- name    : OrderClosures.regularOpenOfClopen_eq_sSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:35.834783+00:00
-- url     : https://prove2.me/theorems/1fd6bde4-50cf-4da0-8e3f-9b6bb05c80ca
-- title:
--   Order Closures: regular Open Of Clopen eq s Sup
-- statement:
--   Expresses a clopen union as a supremum of regular-open elements; used to
--   derive the explicit Solovay generator formulas.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L130-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L130-L151

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

theorem OrderClosures.regularOpenOfClopen_eq_sSup {X : Type u} [TopologicalSpace X]
    (S : Set (RegularOpen X)) (t : Set X) (ht : IsClopen t)
    (hunion : t = ⋃ U ∈ S,
      ((((U : RegularOpen X) : TopologicalSpace.Opens X) : Set X))) :
    regularOpenOfClopen t ht = sSup S := by sorry
