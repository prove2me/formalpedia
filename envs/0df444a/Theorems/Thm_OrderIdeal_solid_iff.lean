-- Prove2me | Theorems.Thm_OrderIdeal_solid_iff
-- name    : OrderIdeal.solid_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:19.678538+00:00
-- url     : https://prove2.me/theorems/c39db607-ad64-49fa-941e-b626c6ba73dc
-- title:
--   Order Ideal: solid iff
-- statement:
--   A submodule is the carrier of an order ideal iff it is solid.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L108-L128
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L108-L128

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)

theorem OrderIdeal.solid_iff (M : Submodule ℝ X) :
    (∀ x y : X, x ∈ M → |y| ≤ |x| → y ∈ M) ↔
      (∀ x y : X, x ∈ M → 0 ≤ y → y ≤ x → y ∈ M) ∧
        ∀ x y : X, x ∈ M → y ∈ M → x ⊔ y ∈ M := by sorry
