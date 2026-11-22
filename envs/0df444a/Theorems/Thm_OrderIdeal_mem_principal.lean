-- Prove2me | Theorems.Thm_OrderIdeal_mem_principal
-- name    : OrderIdeal.mem_principal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:34.056816+00:00
-- url     : https://prove2.me/theorems/49663c17-1b43-4d84-9e54-760bb0a0aaaf
-- title:
--   Order Ideal: mem principal
-- statement:
--   Characterisation of membership in the principal ideal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L315-L316
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L315-L316

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

theorem OrderIdeal.mem_principal {a x : X} :
    x ∈ principal a ↔ ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • |a| := by sorry
