-- Prove2me | Theorems.Thm_OrderClosures_ordinalProjection_chain_iSup
-- name    : OrderClosures.ordinalProjection_chain_iSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:17.910799+00:00
-- url     : https://prove2.me/theorems/48bb7577-5d53-4f34-8af3-8a2cdb6bf737
-- title:
--   Order Closures: ordinal Projection chain i Sup
-- statement:
--   Claim 2 in the proof of Theorem `thm:solid-iterations`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L754-L866
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L754-L866

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.ordinalProjection_chain_iSup
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hne : Z.Nonempty)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1) :
    IsLUB (ordinalProjection ξ '' Z) (ordinalProjection ξ α) := by sorry
