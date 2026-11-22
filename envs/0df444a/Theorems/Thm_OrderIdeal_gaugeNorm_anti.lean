-- Prove2me | Theorems.Thm_OrderIdeal_gaugeNorm_anti
-- name    : OrderIdeal.gaugeNorm_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:52.47894+00:00
-- url     : https://prove2.me/theorems/784920c2-7a92-476a-9374-d69c89f76cf1
-- title:
--   Order Ideal: gauge Norm anti
-- statement:
--   If `0 ≤ e ≤ u` then `‖·‖_u ≤ ‖·‖_e` on `I_e`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L510-L517
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L510-L517

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
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (a : X)

theorem OrderIdeal.gaugeNorm_anti {e u : X} (he : 0 ≤ e) (heu : e ≤ u)
    {x : X} (hx : x ∈ principal e) : gaugeNorm u x ≤ gaugeNorm e x := by sorry
