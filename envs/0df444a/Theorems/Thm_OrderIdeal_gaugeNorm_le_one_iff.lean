-- Prove2me | Theorems.Thm_OrderIdeal_gaugeNorm_le_one_iff
-- name    : OrderIdeal.gaugeNorm_le_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:21.04082+00:00
-- url     : https://prove2.me/theorems/97e59b2f-55c6-475f-92f9-36f7f7b19d32
-- title:
--   Order Ideal: gauge Norm le one iff
-- statement:
--   The closed unit ball of the gauge norm is the order interval
--   `[-|a|, |a|]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L499-L507
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L499-L507

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

theorem OrderIdeal.gaugeNorm_le_one_iff [IsVLArchimedean X] {x : X} (hx : x ∈ principal a) :
    gaugeNorm a x ≤ 1 ↔ |x| ≤ |a| := by sorry
