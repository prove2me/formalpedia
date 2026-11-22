-- Prove2me | Theorems.Thm_OrderClosures_treeBandProjection_support_nonempty_iff
-- name    : OrderClosures.treeBandProjection_support_nonempty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:02:22.236939+00:00
-- url     : https://prove2.me/theorems/5c064d34-f209-421e-9be6-23117c184b33
-- title:
--   Order Closures: tree Band Projection support nonempty iff
-- statement:
--   Characterizes when a band projection has nonempty support; used to define
--   and track recurrent bands.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L92-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L92-L106

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

theorem OrderClosures.treeBandProjection_support_nonempty_iff (n : ℕ)
    (B : TreeBandIndex n) (w : TreeCoefficients n) :
    (treeBandProjection n B w).support.Nonempty ↔
      ∃ t ∈ w.support, treeBandOfNode n t = B := by sorry
