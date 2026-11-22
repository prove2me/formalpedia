-- Prove2me | Theorems.Thm_OrderClosures_finiteBandProjection_le
-- name    : OrderClosures.finiteBandProjection_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:43.283571+00:00
-- url     : https://prove2.me/theorems/6962d98e-3497-4592-aebe-b65a2daf9685
-- title:
--   Order Closures: finite Band Projection le
-- statement:
--   A finite band projection decreases nonnegative coefficient vectors.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L151-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L151-L157

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

theorem OrderClosures.finiteBandProjection_le (n : ℕ) (Λ : Finset (TreeBandIndex n))
    {w : TreeCoefficients n} (hw : 0 ≤ w) : finiteBandProjection n Λ w ≤ w := by sorry
