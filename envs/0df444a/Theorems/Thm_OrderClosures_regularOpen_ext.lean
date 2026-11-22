-- Prove2me | Theorems.Thm_OrderClosures_regularOpen_ext
-- name    : OrderClosures.regularOpen_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:46.433935+00:00
-- url     : https://prove2.me/theorems/ea87f0c7-ee68-4d8e-916a-eb8b3f37d15f
-- title:
--   Order Closures: regular Open ext
-- statement:
--   Reduces equality of regular open sets to equality of carriers; used to
--   simplify Boolean-algebra computations in the Solovay construction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L80-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L80-L85

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

theorem OrderClosures.regularOpen_ext {X : Type u} [TopologicalSpace X]
    {U V : RegularOpen X}
    (h : (((U : TopologicalSpace.Opens X) : Set X)) =
      (((V : TopologicalSpace.Opens X) : Set X))) : U = V := by sorry
