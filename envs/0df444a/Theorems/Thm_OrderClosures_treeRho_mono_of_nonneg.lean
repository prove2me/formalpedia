-- Prove2me | Theorems.Thm_OrderClosures_treeRho_mono_of_nonneg
-- name    : OrderClosures.treeRho_mono_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:57.155626+00:00
-- url     : https://prove2.me/theorems/35af67df-133c-4384-8f62-46e158963b9e
-- title:
--   Order Closures: tree Rho mono of nonneg
-- statement:
--   Shows coefficientwise monotonicity of `treeRho` on the positive cone;
--   used to compare band projections and trimmed coefficients.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L98-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L98-L110

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.treeRho_mono_of_nonneg (n : ℕ) {u v : TreeCoefficients n}
    (hu : 0 ≤ u) (huv : u ≤ v) : treeRho n u ≤ treeRho n v := by sorry
