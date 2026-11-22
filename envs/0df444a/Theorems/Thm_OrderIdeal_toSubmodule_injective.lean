-- Prove2me | Theorems.Thm_OrderIdeal_toSubmodule_injective
-- name    : OrderIdeal.toSubmodule_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:25.215933+00:00
-- url     : https://prove2.me/theorems/a552bf22-761f-454c-8fe6-9a5d0c5e7d2e
-- title:
--   Order Ideal: to Submodule injective
-- statement:
--   The coercion to `Submodule ℝ X` is injective.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L131-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L131-L136

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Theorems.Thm_VectorSublattice_toSubmodule_injective

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)

theorem OrderIdeal.toSubmodule_injective :
    Function.Injective
      (fun J : OrderIdeal X => J.toSubmodule) := by sorry
