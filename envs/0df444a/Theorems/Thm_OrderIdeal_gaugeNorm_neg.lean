-- Prove2me | Theorems.Thm_OrderIdeal_gaugeNorm_neg
-- name    : OrderIdeal.gaugeNorm_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:32.955849+00:00
-- url     : https://prove2.me/theorems/57f65cb6-fed5-4e68-87b7-65d060c60812
-- title:
--   Order Ideal: gauge Norm neg
-- statement:
--   The gauge norm is symmetric.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L365-L367
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L365-L367

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

theorem OrderIdeal.gaugeNorm_neg (x : X) :
    gaugeNorm a (-x) = gaugeNorm a x := by sorry
