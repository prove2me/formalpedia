-- Prove2me | Theorems.Thm_GeometryOfGraphs_Clique_disjoint_interiors
-- name    : GeometryOfGraphs.Clique.disjoint_interiors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:09:59.053221+00:00
-- url     : https://prove2.me/theorems/755f7d6b-d874-43cf-8645-75294bd0b480
-- title:
--   Proposition 5.4 proof — disjoint interiors of convex-hull translates
-- statement:
--   Let $n\ge1$, and let $x_1,\ldots,x_n$ be pairwise at norm-distance one in a $d$-dimensional real normed space. Set $D=\operatorname{conv}\{x_1,\ldots,x_n\}$. For distinct indices $i,j$, the translates $D+x_i$ and $D+x_j$ have disjoint interiors:
--
--   $$
--   \operatorname{int}\bigl((D+x_i)\cap(D+x_j)\bigr)=\varnothing.
--   $$
--
--   This is the separation claim preceding the volume comparison in Proposition 5.4.
--
--   **Formalization Note** Interior is taken in the ordinary topology of $\mathbb R^d$, which agrees with the topology induced by every norm on this finite-dimensional space.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 231, proof of Proposition 5.4, first claim

import Definitions.Def_GeometryOfGraphs_Clique_isoDim

namespace GeometryOfGraphs.Clique

/-- Disjoint interiors of the translates `D + xᵢ`, Proposition 5.4, p. 231. -/
theorem disjoint_interiors {n d : ℕ} (hn : 0 < n) (N : (Fin d → ℝ) → ℝ)
    (hN : IsNormFun N) (x : Fin n → (Fin d → ℝ))
    (hx : ∀ i j, i ≠ j → N (x i - x j) = 1)
    (i j : Fin n) (hij : i ≠ j) :
    interior (((fun y => y + x i) '' convexHull ℝ (Set.range x)) ∩
      ((fun y => y + x j) '' convexHull ℝ (Set.range x))) = ∅ := by sorry

end GeometryOfGraphs.Clique
