-- Prove2me | Theorems.Thm_OrderClosures_leastCNFExponent_chain_lub_le
-- name    : OrderClosures.leastCNFExponent_chain_lub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:00.222424+00:00
-- url     : https://prove2.me/theorems/52483c1d-196b-410e-ad53-3dba3a794f28
-- title:
--   Order Closures: least CNFExponent chain lub le
-- statement:
--   Controls the least CNF exponent of a chain supremum; used to keep the
--   supremum projection inside the required Gao stage.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L659-L751
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/OrdinalSpace.lean#L659-L751

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_CNFOrder
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_OrdinalSpace
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.leastCNFExponent_chain_lub_le
    (ξ γ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hne : Z.Nonempty)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1)
    (hleast : ∀ ζ ∈ Z, leastCNFExponent ζ.1 < γ) :
    leastCNFExponent α.1 ≤ γ := by sorry
