-- Prove2me | Theorems.Thm_OrderClosures_treeRho_finiteBandProjection
-- name    : OrderClosures.treeRho_finiteBandProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:46.9508+00:00
-- url     : https://prove2.me/theorems/20b58ea3-a5d3-4daa-887f-108c18888fed
-- title:
--   Order Closures: tree Rho finite Band Projection
-- statement:
--   Expresses the mass of a finite band projection as a finite sum; used for
--   tail-mass estimates in the trimming lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L161-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L161-L209

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

theorem OrderClosures.treeRho_finiteBandProjection (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    treeRho n (finiteBandProjection n Λ w) =
      ∑ B ∈ Λ, treeRho n (treeBandProjection n B w) := by sorry
