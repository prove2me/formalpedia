-- Prove2me | Theorems.Thm_OrderClosures_mem_bandsAt_iff
-- name    : OrderClosures.mem_bandsAt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:17.569204+00:00
-- url     : https://prove2.me/theorems/24525155-23d4-40b3-823c-ed8f8111b3dc
-- title:
--   Order Closures: mem bands At iff
-- statement:
--   Characterizes the finite set of bands occurring in a coefficient vector;
--   used in the thinning recursion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L117-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L117-L122

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

theorem OrderClosures.mem_bandsAt_iff (n : ℕ) (w : TreeCoefficients n)
    (B : TreeBandIndex n) :
    B ∈ bandsAt n w ↔ (treeBandProjection n B w).support.Nonempty := by sorry
