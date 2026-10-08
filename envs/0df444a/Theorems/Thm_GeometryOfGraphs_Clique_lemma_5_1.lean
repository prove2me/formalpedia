-- Prove2me | Theorems.Thm_GeometryOfGraphs_Clique_lemma_5_1
-- name    : GeometryOfGraphs.Clique.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:09:21.994338+00:00
-- url     : https://prove2.me/theorems/72af5f5b-5e8f-49cb-b5df-73df935baddc
-- title:
--   Lemma 5.1 — finite Fréchet embedding into ℓ∞
-- statement:
--   Let $(X,\delta)$ be a finite pseudometric space with $m$ points. There is a map $\varphi:X\to\mathbb R^m$ such that
--
--   $$
--   \max_{1\le k\le m}\left|\varphi(x)_k-\varphi(y)_k\right|=\delta(x,y)
--   \qquad\text{for all }x,y\in X.
--   $$
--
--   Thus every finite metric space embeds isometrically into $\ell_\infty^m$, establishing that its isometric dimension is defined by a nonempty set of dimensions.
--
--   **Formalization Note** The coordinatewise upper bounds and an attained coordinate express the maximum without taking a supremum over an empty coordinate set. An empty space is included, where the pairwise assertion has no instances.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 229, Lemma 5.1

import Definitions.Def_GeometryOfGraphs_Clique_isoDim

namespace GeometryOfGraphs.Clique

/-- Lemma 5.1, p. 229: the finite Fréchet embedding into ℓ∞. -/
theorem lemma_5_1 (X : Type*) [Fintype X] [PseudoMetricSpace X] :
    ∃ φ : X → (Fin (Fintype.card X) → ℝ),
      ∀ x y, (∀ k, |φ x k - φ y k| ≤ dist x y) ∧
        ∃ k, |φ x k - φ y k| = dist x y := by sorry

end GeometryOfGraphs.Clique
