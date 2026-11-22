-- Prove2me | Theorems.Thm_OrderClosures_finiteBandProjection_apply
-- name    : OrderClosures.finiteBandProjection_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:19.718805+00:00
-- url     : https://prove2.me/theorems/0a8eeca3-9d78-447d-82f8-86a31db3358c
-- title:
--   Order Closures: finite Band Projection apply
-- statement:
--   Gives the pointwise formula for projection onto finitely many bands; used
--   to decompose coefficients in trimming and moderatedness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L126-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L126-L138

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

theorem OrderClosures.finiteBandProjection_apply (n : ℕ) (Λ : Finset (TreeBandIndex n))
    (w : TreeCoefficients n) (t : TreeNode n) :
    (treeBandOfNode n t ∈ Λ → finiteBandProjection n Λ w t = w t) ∧
      (treeBandOfNode n t ∉ Λ → finiteBandProjection n Λ w t = 0) := by sorry
