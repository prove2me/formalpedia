-- Prove2me | Theorems.Thm_OrderClosures_regularOpenOfClopen_congr
-- name    : OrderClosures.regularOpenOfClopen_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:18.403805+00:00
-- url     : https://prove2.me/theorems/285bfa53-e68c-4d23-a1d8-96f46569f38a
-- title:
--   Order Closures: regular Open Of Clopen congr
-- statement:
--   Makes the regular-open constructor respect equality of clopen carriers;
--   used when rewriting cylinder identities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L89-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L89-L93

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

theorem OrderClosures.regularOpenOfClopen_congr {X : Type u} [TopologicalSpace X]
    {s t : Set X} (hs : IsClopen s) (ht : IsClopen t) (h : s = t) :
    regularOpenOfClopen s hs = regularOpenOfClopen t ht := by sorry
