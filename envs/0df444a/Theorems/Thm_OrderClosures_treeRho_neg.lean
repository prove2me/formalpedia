-- Prove2me | Theorems.Thm_OrderClosures_treeRho_neg
-- name    : OrderClosures.treeRho_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:12:35.167988+00:00
-- url     : https://prove2.me/theorems/b1199cd1-77c1-47d9-8e6e-317e2ceb314b
-- title:
--   Order Closures: tree Rho neg
-- statement:
--   Shows that `treeRho` is invariant under negation; used for symmetry of the
--   bundled lattice seminorm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L59-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/TreeNorm.lean#L59-L63

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

theorem OrderClosures.treeRho_neg (n : ℕ) (w : TreeCoefficients n) :
    treeRho n (-w) = treeRho n w := by sorry
