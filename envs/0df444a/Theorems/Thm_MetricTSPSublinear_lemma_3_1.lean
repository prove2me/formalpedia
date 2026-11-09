-- Prove2me | Theorems.Thm_MetricTSPSublinear_lemma_3_1
-- name    : MetricTSPSublinear.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:33:28.359868+00:00
-- url     : https://prove2.me/theorems/0f99a895-2592-42f1-9b21-88d0eab3ebbd
-- title:
--   Lemma 3.1 — pairwise-intersecting subtrees of $R(T)$ have a common point
-- statement:
--   Let $T$ be a finite tree and $R(T)$ its continuous extension. If $X_1,\dots,X_k$ are subtrees of $R(T)$ (closed connected subsets) such that $X_i\cap X_j\neq\emptyset$ for all $i,j$, then there is a point $p\in R(T)$ with
--   $$p\in X_1\cap\cdots\cap X_k.$$
--
--   In other words, subtrees of $R(T)$ have Helly number $2$. The paper uses this to show that the region of admissible positions of a vertex on the computed core is nonempty (Lemma 5.3).
--
--   Differences from the source:
--   - encoding: a tree T with edge weights and its continuous extension R(T) → a tree G on Fin m, points of R(G) as nodes or (edge, α), no weights; reason: the lemma uses no weights; the points of R(T) do not depend on them
--   - encoding: subtree = a closed connected subset of R(T) (footnote 5) → IsSubtree: nonempty, geodesically convex, closed in the unit-length metric; reason: in a tree connected subsets are the geodesically convex ones, and all positive lengths give the same topology
--   - encoding: any finite collection of subtrees → a family indexed by Fin k, k = 0 allowed; reason: for k = 0 the conclusion is that R(T) is nonempty, which holds
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §3, Lemma 3.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_MetricTSPSublinear_IsSubtree

namespace MetricTSPSublinear

/-- **Lemma 3.1 (Helly property of subtrees of `R(T)`).**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §3, p.10 (PDF p.12): "Any finite collection of pairwise-intersecting subtrees F has a common point, which is a
member of every subtree."

For every finite tree `G` on `Fin m` and every finite family `X : Fin k → Set (RPoint G)` of subtrees of `R(G)`
that pairwise intersect, some point of `R(G)` lies in every member.

**Formalization Note.** Subtrees are `IsSubtree` (nonempty, geodesically convex, closed: footnote 5's "closed
connected subset"). The lemma uses no edge weights. A finite collection is indexed by `Fin k`; for `k = 0` the
conclusion says that `R(G)` is nonempty, which holds because a tree is. -/
theorem lemma_3_1 {m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.IsTree) (k : ℕ) (X : Fin k → Set (RPoint G))
    (hX : ∀ i, IsSubtree G hG (X i)) (hint : ∀ i j, (X i ∩ X j).Nonempty) :
    ∃ p : RPoint G, ∀ i, p ∈ X i := by sorry

end MetricTSPSublinear
