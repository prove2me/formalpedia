-- Prove2me | Theorems.Thm_OrderClosures_treeRho_bandProjection_le
-- name    : OrderClosures.treeRho_bandProjection_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:34.937137+00:00
-- url     : https://prove2.me/theorems/d2cc9460-87e8-4975-924d-8048eb97e5d5
-- title:
--   Order Closures: tree Rho band Projection le
-- statement:
--   A single band projection cannot increase `treeRho`; used to uniformly
--   bound each coordinate in the sharp-subsequence extraction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L345-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L345-L359

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

theorem OrderClosures.treeRho_bandProjection_le (n : ℕ) (B : TreeBandIndex n)
    (w : TreeCoefficients n) :
    treeRho n (treeBandProjection n B w) ≤ treeRho n w := by sorry
