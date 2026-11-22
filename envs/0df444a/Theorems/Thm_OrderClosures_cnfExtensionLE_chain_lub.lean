-- Prove2me | Theorems.Thm_OrderClosures_cnfExtensionLE_chain_lub
-- name    : OrderClosures.cnfExtensionLE_chain_lub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:01:42.778613+00:00
-- url     : https://prove2.me/theorems/02120654-4978-49d7-972e-e2814beb5512
-- title:
--   Order Closures: cnf Extension LE chain lub
-- statement:
--   Proves that the ordinary supremum of a nonempty extension chain remains
--   above every member in `cnfExtensionLE`; used by `ordinalProjection_chain_iSup`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L549-L655
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L549-L655

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.cnfExtensionLE_chain_lub
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1) :
    ∀ ζ ∈ Z, cnfExtensionLE ζ.1 α.1 := by sorry
