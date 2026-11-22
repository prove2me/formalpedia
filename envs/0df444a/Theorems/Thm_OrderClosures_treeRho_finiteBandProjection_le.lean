-- Prove2me | Theorems.Thm_OrderClosures_treeRho_finiteBandProjection_le
-- name    : OrderClosures.treeRho_finiteBandProjection_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:44.973437+00:00
-- url     : https://prove2.me/theorems/7ef7999b-3de7-4330-a014-f408d4d35b99
-- title:
--   Order Closures: tree Rho finite Band Projection le
-- statement:
--   A projection onto finitely many bands cannot increase `treeRho`; used in
--   the coefficient decomposition for `component_moderated`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L363-L388
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L363-L388

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

theorem OrderClosures.treeRho_finiteBandProjection_le (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    treeRho n (finiteBandProjection n Λ w) ≤ treeRho n w := by sorry
