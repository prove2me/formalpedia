-- Prove2me | Theorems.Thm_OrderClosures_clopenIndicator_union
-- name    : OrderClosures.clopenIndicator_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:12.472932+00:00
-- url     : https://prove2.me/theorems/05f13599-f1a6-4980-894f-1955fdca0807
-- title:
--   Order Closures: clopen Indicator union
-- statement:
--   Computes the supremum of two clopen indicators; used in the Boolean-to-
--   vector-sublattice transfer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1119-L1124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1119-L1124

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
variable (K : Type u) [TopologicalSpace K]

theorem OrderClosures.clopenIndicator_union (s t : Set K) (hs : IsClopen s) (ht : IsClopen t) :
    clopenIndicator K (s ∪ t) (hs.union ht) =
      clopenIndicator K s hs ⊔ clopenIndicator K t ht := by sorry
