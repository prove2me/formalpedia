-- Prove2me | Theorems.Thm_OrderClosures_regularOpenOfClopen_inf
-- name    : OrderClosures.regularOpenOfClopen_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:20.978157+00:00
-- url     : https://prove2.me/theorems/ed71251c-29ab-4179-9caf-ba29eb6916a5
-- title:
--   Order Closures: regular Open Of Clopen inf
-- statement:
--   Computes intersections of clopen sets inside the regular-open algebra;
--   used for finite cylinder meets and Boolean subalgebras.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L97-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L97-L102

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

theorem OrderClosures.regularOpenOfClopen_inf {X : Type u} [TopologicalSpace X]
    (s t : Set X) (hs : IsClopen s) (ht : IsClopen t) :
    regularOpenOfClopen (s ∩ t) (hs.inter ht) =
      regularOpenOfClopen s hs ⊓ regularOpenOfClopen t ht := by sorry
