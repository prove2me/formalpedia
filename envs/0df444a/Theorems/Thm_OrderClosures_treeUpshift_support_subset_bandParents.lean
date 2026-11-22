-- Prove2me | Theorems.Thm_OrderClosures_treeUpshift_support_subset_bandParents
-- name    : OrderClosures.treeUpshift_support_subset_bandParents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:04:25.426835+00:00
-- url     : https://prove2.me/theorems/ba43a4ae-5540-4d83-9621-58b6a700f90d
-- title:
--   Order Closures: tree Upshift support subset band Parents
-- statement:
--   Bounds the support of an upshift by the finite set of band parents; used
--   to obtain a finite-dimensional convergent subsequence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L240-L255
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L240-L255

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

theorem OrderClosures.treeUpshift_support_subset_bandParents (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    (treeUpshift n (finiteBandProjection n Λ w)).support ⊆
      treeBandParents n Λ := by sorry
