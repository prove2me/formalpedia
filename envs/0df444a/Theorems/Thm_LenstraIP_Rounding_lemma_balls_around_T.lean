-- Prove2me | Theorems.Thm_LenstraIP_Rounding_lemma_balls_around_T
-- name    : LenstraIP.Rounding.lemma_balls_around_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:06:03.536063+00:00
-- url     : https://prove2.me/theorems/c525c8ee-a876-4a22-a173-c089fcf23dfe
-- title:
--   §2, p. 543, LEMMA — B(p,r) ⊂ S ⊂ T_c ⊂ B(p,R) with (R/r)² = c²n³ + (c²+1)n² (n even), c²n³ + (2c²−2c+1)n² + (c²−2c)n (n odd)
-- statement:
--   Let $n \ge 1$ and $c \ge 1$. Let $z_0, z_1, \dots, z_n \in \mathbb R^n$ span a regular $n$-simplex $S = \mathrm{conv}\{z_0, \dots, z_n\}$, let $p = (n+1)^{-1}\sum_{j=0}^n z_j$ be its centroid, and let
--   $$T_c = \{x \in \mathbb R^n : \mathrm{vol}(z_0, \dots, z_{i-1}, x, z_{i+1}, \dots, z_n) \le c \cdot \mathrm{vol}(z_0, \dots, z_n) \text{ for all } i \in \{0, 1, \dots, n\}\}.$$
--   Then there are two positive real numbers $r, R$ with $B(p, r) \subseteq S \subseteq T_c \subseteq B(p, R)$ and
--   $$\Big(\frac{R}{r}\Big)^2 = \begin{cases} c^2n^3 + (c^2+1)n^2 & \text{if } n \text{ is even},\\ c^2n^3 + (2c^2 - 2c + 1)n^2 + (c^2 - 2c)n & \text{if } n \text{ is odd}.\end{cases}$$
--   Here $B(p, \rho) = \{x \in \mathbb R^n : |x - p| \le \rho\}$ and $\mathrm{vol}$ is the simplex volume $|\det M|/n!$.
--
--   With $c = 3/2$ this LEMMA gives the constant $c_1 = 2n^{3/2}$ of the mission's goal; Remark (c) of the paper uses it for other values of $c$.
--
--   **Formalization Note** "With the above notation" refers to $z_j = \tau(v_j)$; the LEMMA uses only that the $z_j$ span a regular simplex, so it is stated for any regular simplex `z : Fin (n+1) → EuclideanSpace ℝ (Fin n)`, regularity meaning all pairwise distances equal and positive. "Two positive real numbers $r, R$" is $\exists\, r\, R,\ 0 < r \wedge 0 < R \wedge \dots$, with the paper's equality for $(R/r)^2$. $n \ge 1$ is assumed (the paper works in $\mathbb R^n$ with an $n$-simplex of positive volume).
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §2, p. 543, LEMMA

import Mathlib
import Definitions.Def_LenstraIP_Rounding_SimplexData

namespace LenstraIP.Rounding

theorem lemma_balls_around_T {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 1 ≤ c)
    (z : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) (hz : IsRegular z) :
    ∃ r R : ℝ, 0 < r ∧ 0 < R ∧
      Metric.closedBall (centroid z) r ⊆ convexHull ℝ (Set.range z) ∧
      convexHull ℝ (Set.range z) ⊆ Tset c z ∧
      Tset c z ⊆ Metric.closedBall (centroid z) R ∧
      (R / r) ^ 2 =
        (if Even n then c ^ 2 * (n : ℝ) ^ 3 + (c ^ 2 + 1) * (n : ℝ) ^ 2
         else c ^ 2 * (n : ℝ) ^ 3 + (2 * c ^ 2 - 2 * c + 1) * (n : ℝ) ^ 2 + (c ^ 2 - 2 * c) * (n : ℝ)) := by sorry

end LenstraIP.Rounding
