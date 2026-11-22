-- Prove2me | Theorems.Thm_OrderClosures_clopenIndicator_inter
-- name    : OrderClosures.clopenIndicator_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:06.412461+00:00
-- url     : https://prove2.me/theorems/d6b28aa7-dff9-4f4a-9111-4c310304f091
-- title:
--   Order Closures: clopen Indicator inter
-- statement:
--   Computes the infimum of two clopen indicators; used to make Boolean
--   indicators compatible with lattice operations.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1110-L1115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L1110-L1115

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

theorem OrderClosures.clopenIndicator_inter (s t : Set K) (hs : IsClopen s) (ht : IsClopen t) :
    clopenIndicator K (s ∩ t) (hs.inter ht) =
      clopenIndicator K s hs ⊓ clopenIndicator K t ht := by sorry
