-- Prove2me | Theorems.Thm_LenstraIP_Rounding_modelT_eq_convexHull
-- name    : LenstraIP.Rounding.modelT_eq_convexHull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:05:44.019761+00:00
-- url     : https://prove2.me/theorems/8593dd38-7b6b-4cf1-9e34-69e661732bfb
-- title:
--   §2, pp. 543–544 — T_c is the convex hull of the coordinate permutations of one point
-- statement:
--   Let $n \ge 1$ and $c \ge 1$, and let $e_0, \dots, e_n$ be the standard basis of $\mathbb R^{n+1}$. In the coordinates of the proof of the LEMMA, the set $T_c$ is
--   $$T_c = \Big\{ (r_j)_{j=0}^n \in \mathbb R^{n+1} : |r_j| \le c \text{ for } 0 \le j \le n, \text{ and } \sum_{j=0}^n r_j = 1 \Big\}.$$
--   (The volume ratio $\mathrm{vol}(z_0, \dots, x, \dots, z_n)/\mathrm{vol}(z_0, \dots, z_n)$ with $x$ in place of $z_i$ is $|r_i|$ in these coordinates.) The theorem asserts that $T_c$ is the convex hull of the set of points obtained by permuting the coordinates of the point
--   $$e_0 - c\sum_{j=1}^m e_j + c\sum_{j=m+1}^n e_j \ \text{ if } n = 2m, \qquad (1-c)e_0 - c\sum_{j=1}^m e_j + c\sum_{j=m+1}^n e_j \ \text{ if } n = 2m+1.$$
--
--   Geometrically, $T_c$ is the slice of the cube $[-c, c]^{n+1}$ by the hyperplane $\sum_j r_j = 1$, and the theorem lists its vertices. It is the first step of the proof of the LEMMA: it reduces the outer radius of $T_c$ to the distance of one point.
--
--   **Formalization Note** The set is `modelT n c`, the point `modelPt n c`, and the permuted point `permuteCoords σ x` has coordinates $x_{\sigma(j)}$; the convex hull is over all permutations $\sigma$ of `Fin (n+1)`. $\mathbb R^{n+1}$ is `EuclideanSpace ℝ (Fin (n+1))`, and $m$ is `n / 2`.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §2, pp. 543–544 (proof of the LEMMA): 'By a straightforward analysis one proves that T_c is the convex hull of the set of points obtained by permuting the coordinates of the point …'

import Mathlib
import Definitions.Def_LenstraIP_Rounding_SimplexData

namespace LenstraIP.Rounding

theorem modelT_eq_convexHull {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 1 ≤ c) :
    modelT n c =
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin (n + 1)) => permuteCoords σ (modelPt n c)) := by sorry

end LenstraIP.Rounding
