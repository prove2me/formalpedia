-- Prove2me | Theorems.Thm_InterpOptStop_SAA_Supplement_lemma_EC_4
-- name    : InterpOptStop.SAA.Supplement.lemma_EC_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:46:50.705272+00:00
-- url     : https://prove2.me/theorems/813d22ba-abf7-49ae-9463-3ca462b43b86
-- title:
--   Lemma EC.4 — exact finite-box representation
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ and let $B_j=\prod_{i=1}^n(a^j_i,b^j_i]$ be any finite collection of boxes. Then an actual finite binary threshold tree with the published evaluation convention represents the box policy exactly:
--   $$\exists\pi_{\rm tree}\quad\forall x\in\mathcal X,\quad\pi_{\rm tree}(x)=\pi_{\rm boxes}(x).$$
--   The policy stops on the union and continues elsewhere. Overlaps, empty unions, degenerate boxes and zero dimension are included. This supplies the exact representation used for the approximation in Theorem 2.
--
--   Differences from the source:
--   - generalization: the inherited bounded product state space → any set X⊆ℝⁿ, with any finite box family; reason: representation is pointwise and needs no probability, boundedness or product premise; taking the source X specializes to its full claim
--   - encoding: tree policy πtree and half-open boxes → the published Tree n with thresholds and its ≤-left policy; a_i<x_i≤b_i for every coordinate; reason: the witness is an actual finite tree and the split equality case matches the source boxes
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Lemma EC.4, p. ec22

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_Boxes

namespace InterpOptStop.SAA.Supplement

theorem lemma_EC_4 {n K : ℕ} (X : Set (Fin n → ℝ))
    (a b : Fin K → Fin n → ℝ) :
    ∃ (S : Tree n) (θ : Thresholds), ∀ x ∈ X, policy S θ x = boxesPolicy a b x := by sorry

end InterpOptStop.SAA.Supplement
