-- Prove2me | Theorems.Thm_HardcoreSlices_lemmas_3_7_3_8
-- name    : HardcoreSlices.lemmas_3_7_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:10.916965+00:00
-- url     : https://prove2.me/theorems/fada5bf4-74b5-4f1e-bd54-a5d5b187f9e0
-- title:
--   Lemmas 3.7, 3.8 — at most two common neighbours, and no vertex sharing two with two others
-- statement:
--   Let $G$ be a random $\Delta$-regular bipartite graph. With high probability both of the following hold:
--
--   1. every pair of distinct vertices $u,v$ on the same side has $|N(u)\cap N(v)|\le2$;
--   2. no vertex $x$ shares at least $2$ common neighbours with more than one other vertex.
--
--   These are the hypotheses of Lemma 5.1, verified for the random graph.
--
--   Differences from the source:
--   - encoding: two lemmas, each with high probability → one conjunction under one high-probability event; reason: the intersection of two high-probability events is one
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Lemmas 3.7, 3.8, p.17

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Lemmas 3.7 and 3.8.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.17.
Lemma 3.7: "Let `G = (X, Y, E)` be a random `∆`-regular bipartite graph. Then with high probability over the randomness of `G`, every pair of
vertices `u ≠ v ∈ X` or `u ≠ v ∈ Y` satisfies `|N(u) ∩ N(v)| ≤ 2`."
Lemma 3.8: "Let `G = (X, Y, E)` be a random `∆`-regular bipartite graph. Then with high probability over the randomness of `G`, there is no
vertex `x ∈ X` (resp. `Y`) sharing at least 2 common neighbors with more than one other vertex."

**Formalization Note.** One event, as used in the proof of Theorem 1.9. `N(u)` is `vertexBoundary G {u}`. Two vertices on opposite sides have no
common neighbour in a bipartite graph, so the side conditions in the lemmas are automatic for the second clause. -/
theorem lemmas_3_7_3_8 (Δ : ℕ) :
    AlmostEvery Δ (fun m G =>
      (∀ u v : Vertex m, u ≠ v → ((u ∈ oddSide m ∧ v ∈ oddSide m) ∨ (u ∈ evenSide m ∧ v ∈ evenSide m)) →
        (vertexBoundary G {u} ∩ vertexBoundary G {v}).card ≤ 2) ∧
      (∀ x v₁ v₂ : Vertex m, v₁ ≠ x → v₂ ≠ x → v₁ ≠ v₂ →
        2 ≤ (vertexBoundary G {x} ∩ vertexBoundary G {v₁}).card →
        2 ≤ (vertexBoundary G {x} ∩ vertexBoundary G {v₂}).card → False)) := by sorry

end HardcoreSlices
