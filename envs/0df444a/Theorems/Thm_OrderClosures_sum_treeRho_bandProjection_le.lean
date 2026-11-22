-- Prove2me | Theorems.Thm_OrderClosures_sum_treeRho_bandProjection_le
-- name    : OrderClosures.sum_treeRho_bandProjection_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:42.72991+00:00
-- url     : https://prove2.me/theorems/76b948b6-8fb7-4e67-9621-c921985d5812
-- title:
--   Order Closures: sum tree Rho band Projection le
-- statement:
--   Bounds the total mass of any finite band family by the original mass;
--   used to prove summability of limiting band masses in `tree_trim`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L392-L396
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L392-L396

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.sum_treeRho_bandProjection_le (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    ∑ B ∈ Λ, treeRho n (treeBandProjection n B w) ≤ treeRho n w := by sorry
