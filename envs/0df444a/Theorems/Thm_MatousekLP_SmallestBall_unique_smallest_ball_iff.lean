-- Prove2me | Theorems.Thm_MatousekLP_SmallestBall_unique_smallest_ball_iff
-- name    : MatousekLP.SmallestBall.unique_smallest_ball_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T21:54:45.063013+00:00
-- url     : https://prove2.me/theorems/ef54f441-e70a-4e96-8ad6-ca40d67d729e
-- title:
--   Lemma 8.7.3 — boundary characterization of the unique smallest enclosing ball
-- statement:
--   Let $B$ be the closed ball in $\mathbb{R}^d$ with center $s^*$ and radius $r\ge 0$, and let $S=\{s_1,\dots,s_k\}$ be points on the boundary of $B$, i.e. $\|s_j-s^*\|=r$ for all $j$. Then the following two statements are equivalent.
--
--   1. $B$ is the unique smallest enclosing ball of $S$: it contains $S$, every ball containing $S$ has radius at least $r$, and every ball containing $S$ with radius at most $r$ has center $s^*$.
--   2. For every $u\in\mathbb{R}^d$ there is an index $j\in\{1,\dots,k\}$ with
--   $$u^{T}(s_j-s^*)\le 0 .$$
--
--   Condition 2 says that no hyperplane strictly separates $S$ from $s^*$. The lemma characterizes smallest enclosing balls by their boundary points and is the geometric half of the proof of Theorem 8.7.4.
--
--   **Formalization Note** The points are indexed by `Fin k` (0-based) and $S$ is their range; $u^T(s_j-s^*)$ is the Euclidean inner product. For $k=0$ both statements are false (a ball of negative radius, which is empty, encloses $S=\emptyset$; and no index exists), so no hypothesis $k\ge 1$ is needed.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 188, Lemma 8.7.3

import Mathlib
import Definitions.Def_MatousekLP_SmallestBall_Basic

open scoped RealInnerProductSpace

namespace MatousekLP.SmallestBall

/-- Lemma 8.7.3 (Matoušek & Gärtner, p. 188). Let `S = {s₁, …, s_k} ⊆ ℝ^d` lie on the boundary of
the ball `B` with center `s*` and radius `r` (so `‖sⱼ − s*‖ = r` for all `j`). Then `B` is the
unique smallest enclosing ball of `S` iff for every `u ∈ ℝ^d` there is an index `j` with
`uᵀ(sⱼ − s*) ≤ 0`. -/
theorem unique_smallest_ball_iff {d k : ℕ} (s : Fin k → EuclideanSpace ℝ (Fin d))
    (sstar : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 ≤ r)
    (hbd : ∀ j, dist (s j) sstar = r) :
    IsUniqueSmallestEnclosingBall (Set.range s) sstar r ↔
      ∀ u : EuclideanSpace ℝ (Fin d), ∃ j : Fin k, ⟪u, s j - sstar⟫ ≤ 0 := by sorry

end MatousekLP.SmallestBall
