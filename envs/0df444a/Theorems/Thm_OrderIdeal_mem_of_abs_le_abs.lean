-- Prove2me | Theorems.Thm_OrderIdeal_mem_of_abs_le_abs
-- name    : OrderIdeal.mem_of_abs_le_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:27:23.346349+00:00
-- url     : https://prove2.me/theorems/597aaeb8-4413-4d87-996b-e26df4b1af81
-- title:
--   Order Ideal: mem of abs le abs
-- statement:
--   Solidity in terms of absolute value: `x ∈ J` and `|y| ≤ |x|` imply
--   `y ∈ J`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L77-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Ideal.lean#L77-L79

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

theorem OrderIdeal.mem_of_abs_le_abs {x y : X} (hx : x ∈ J)
    (h : |y| ≤ |x|) : y ∈ J := by sorry
