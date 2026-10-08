-- Prove2me | Theorems.Thm_GeometryOfGraphs_Clique_difference_body
-- name    : GeometryOfGraphs.Clique.difference_body
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:15.448753+00:00
-- url     : https://prove2.me/theorems/6027c719-6cef-454b-94d6-2d777ff8b6cb
-- title:
--   Proposition 5.4 proof — the difference body lies in the unit ball
-- statement:
--   Let $n\ge1$, and let $x_1,\ldots,x_n$ be points of a $d$-dimensional real normed space with norm $N$. Suppose $N(x_i-x_j)=1$ whenever $i\ne j$. Put $D=\operatorname{conv}\{x_1,\ldots,x_n\}$ and let $B=\{z:N(z)\le1\}$ be the unit ball. Then
--
--   $$
--   D-D\subseteq B.
--   $$
--
--   This is the difference-body inclusion used to separate translates of the convex hull in Proposition 5.4.
--
--   **Formalization Note** Membership in $D-D$ is represented by arbitrary $u,v\in D$ and the bound $N(u-v)\le1$. This formulation also covers a one-point set, where the displayed convex-hull identity in the proof has an empty generating set.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 231, proof of Proposition 5.4, difference-body sentence

import Definitions.Def_GeometryOfGraphs_Clique_isoDim

namespace GeometryOfGraphs.Clique

/-- The inclusion `D - D ⊆ 𝔹` in the proof of Proposition 5.4, p. 231. -/
theorem difference_body {n d : ℕ} (hn : 0 < n) (N : (Fin d → ℝ) → ℝ)
    (hN : IsNormFun N) (x : Fin n → (Fin d → ℝ))
    (hx : ∀ i j, i ≠ j → N (x i - x j) = 1)
    (u v : Fin d → ℝ)
    (hu : u ∈ convexHull ℝ (Set.range x))
    (hv : v ∈ convexHull ℝ (Set.range x)) :
    N (u - v) ≤ 1 := by sorry

end GeometryOfGraphs.Clique
