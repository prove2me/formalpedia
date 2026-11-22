-- Prove2me | Theorems.Thm_OrderClosures_tree_thinning
-- name    : OrderClosures.tree_thinning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:05:53.399259+00:00
-- url     : https://prove2.me/theorems/8e161d40-2d1a-46a7-b466-17b84e527277
-- title:
--   Order Closures: tree thinning
-- statement:
--   Paper Lemma `lem:thinning`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L26-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Moderated.lean#L26-L85

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u

theorem OrderClosures.tree_thinning
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hΛ : recurrentBands n w ⊆ (Λ : Set (TreeBandIndex n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w (φ m))).support.Nonempty}.Subsingleton := by sorry
