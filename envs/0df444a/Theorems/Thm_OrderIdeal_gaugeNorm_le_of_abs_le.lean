-- Prove2me | Theorems.Thm_OrderIdeal_gaugeNorm_le_of_abs_le
-- name    : OrderIdeal.gaugeNorm_le_of_abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:21.961852+00:00
-- url     : https://prove2.me/theorems/4322bc23-97cf-48b9-a932-0323b1080fbc
-- title:
--   Order Ideal: gauge Norm le of abs le
-- statement:
--   Any admissible constant bounds the gauge norm from above.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L473-L475
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L473-L475

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

theorem OrderIdeal.gaugeNorm_le_of_abs_le {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : |x| ≤ c • |a|) : gaugeNorm a x ≤ c := by sorry
