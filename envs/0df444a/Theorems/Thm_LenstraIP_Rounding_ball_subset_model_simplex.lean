-- Prove2me | Theorems.Thm_LenstraIP_Rounding_ball_subset_model_simplex
-- name    : LenstraIP.Rounding.ball_subset_model_simplex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:05:53.650294+00:00
-- url     : https://prove2.me/theorems/4defa631-c795-4534-a4cc-50bef21bfbbf
-- title:
--   §2, p. 544 — B(p, r) ⊂ S with r the distance of p to (0, 1/n, …, 1/n), r² = 1/(n(n+1))
-- statement:
--   Let $n \ge 1$. In $\mathbb R^{n+1}$, let $p = \big(\tfrac1{n+1}, \dots, \tfrac1{n+1}\big)$, let $S = \mathrm{conv}\{e_0, \dots, e_n\}$ be the standard simplex, and let $r$ be the distance of $p$ to the point $(0, 1/n, 1/n, \dots, 1/n)$. Then
--   $$r^2 = \frac{1}{n(n+1)},$$
--   and every point $x$ of the hyperplane $\sum_{j=0}^n x_j = 1$ with $|x - p| \le r$ lies in $S$.
--
--   This is the inner radius in the LEMMA's proof: the ball of radius $r$ around the centroid, inside the affine hull of $S$, is contained in $S$.
--
--   **Formalization Note** The paper identifies $\mathbb R^n$ with the hyperplane $\sum_j r_j = 1$, so its ball $B(p, r)$ is the ball *in that hyperplane*; the Lean statement intersects the closed ball of $\mathbb R^{n+1}$ with the hyperplane. (The full ball of $\mathbb R^{n+1}$ is not contained in $S$.) $n \ge 1$ is needed for the point $(0, 1/n, \dots, 1/n)$ to make sense.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §2, p. 544 (proof of the LEMMA): 'Further, B(p, r) ⊂ S, where r is the distance of p to (0, 1/n, 1/n, …, 1/n): r² = 1/(n(n + 1))'

import Mathlib
import Definitions.Def_LenstraIP_Rounding_SimplexData

namespace LenstraIP.Rounding

theorem ball_subset_model_simplex {n : ℕ} (hn : 1 ≤ n) :
    dist (pM n) (facetPt n) ^ 2 = 1 / ((n : ℝ) * ((n : ℝ) + 1)) ∧
      {x : EuclideanSpace ℝ (Fin (n + 1)) | ∑ j, x j = 1} ∩
          Metric.closedBall (pM n) (dist (pM n) (facetPt n)) ⊆ modelS n := by sorry

end LenstraIP.Rounding
