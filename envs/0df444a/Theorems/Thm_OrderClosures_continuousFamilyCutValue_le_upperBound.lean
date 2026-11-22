-- Prove2me | Theorems.Thm_OrderClosures_continuousFamilyCutValue_le_upperBound
-- name    : OrderClosures.continuousFamilyCutValue_le_upperBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:14.555418+00:00
-- url     : https://prove2.me/theorems/a42dc1ee-4a1d-4df0-aecd-1919ba0c6ada
-- title:
--   Order Closures: continuous Family Cut Value le upper Bound
-- statement:
--   Bounds every cut value by any continuous upper bound of the family; used
--   to prove minimality of the constructed supremum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L966-L978
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L966-L978

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
variable (K : Type u) [TopologicalSpace K] [ExtremallyDisconnected K]
omit [ExtremallyDisconnected K]

theorem OrderClosures.continuousFamilyCutValue_le_upperBound {A : Set C(K, ℝ)}
    (hA : A.Nonempty) {h : C(K, ℝ)} (hh : h ∈ upperBounds A) (x : K) :
    continuousFamilySupValue K A x ≤ h x := by sorry
