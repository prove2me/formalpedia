-- Prove2me | Theorems.Thm_OrderClosures_le_lastBandOccurrence
-- name    : OrderClosures.le_lastBandOccurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:51.894905+00:00
-- url     : https://prove2.me/theorems/3fd8b0dd-70e0-41b5-af4d-6b4416959f52
-- title:
--   Order Closures: le last Band Occurrence
-- statement:
--   Bounds every occurrence of a nonrecurrent band by its recorded last index;
--   used to choose a subsequence with transient bands occurring at most once.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L440-L447
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Bands.lean#L440-L447

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

theorem OrderClosures.le_lastBandOccurrence (n : ℕ) (w : ℕ → TreeCoefficients n)
    (B : TreeBandIndex n)
    (hfinite : {m | (treeBandProjection n B (w m)).support.Nonempty}.Finite)
    {m : ℕ} (hm : (treeBandProjection n B (w m)).support.Nonempty) :
    m ≤ lastBandOccurrence n w B := by sorry
