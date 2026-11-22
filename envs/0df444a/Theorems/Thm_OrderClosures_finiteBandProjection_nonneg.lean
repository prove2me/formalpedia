-- Prove2me | Theorems.Thm_OrderClosures_finiteBandProjection_nonneg
-- name    : OrderClosures.finiteBandProjection_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:36.062943+00:00
-- url     : https://prove2.me/theorems/765a10ff-5000-492d-a6d9-f640e29c060e
-- title:
--   Order Closures: finite Band Projection nonneg
-- statement:
--   A finite band projection preserves nonnegativity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L141-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L141-L148

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

theorem OrderClosures.finiteBandProjection_nonneg (n : ℕ) (Λ : Finset (TreeBandIndex n))
    {w : TreeCoefficients n} (hw : 0 ≤ w) : 0 ≤ finiteBandProjection n Λ w := by sorry
