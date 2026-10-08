-- Prove2me | Theorems.Thm_LenstraIP_Rounding_modelT_subset_ball
-- name    : LenstraIP.Rounding.modelT_subset_ball
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:05:50.961698+00:00
-- url     : https://prove2.me/theorems/47b98677-7075-41f0-8e2f-5e270ff4ef9f
-- title:
--   §2, p. 544 — T_c ⊂ B(p, R) with R² = nc² + n/(n+1) (n even), (n+1)c² − 2c + n/(n+1) (n odd)
-- statement:
--   Let $n \ge 1$ and $c \ge 1$. In $\mathbb R^{n+1}$, let $p = \big(\tfrac1{n+1}, \dots, \tfrac1{n+1}\big)$, let $T_c = \{ (r_j)_{j=0}^n : |r_j| \le c \text{ for all } j,\ \sum_j r_j = 1\}$, and let $P$ be the point $e_0 - c\sum_{j=1}^m e_j + c\sum_{j=m+1}^n e_j$ if $n = 2m$ and $(1-c)e_0 - c\sum_{j=1}^m e_j + c\sum_{j=m+1}^n e_j$ if $n = 2m+1$. Let $R = |P - p|$ be the distance of $p$ to this point. Then
--   $$R^2 = \begin{cases} nc^2 + \dfrac{n}{n+1} & \text{if } n \text{ is even},\\[2mm] (n+1)c^2 - 2c + \dfrac{n}{n+1} & \text{if } n \text{ is odd},\end{cases}$$
--   and $T_c \subseteq B(p, R) = \{x \in \mathbb R^{n+1} : |x - p| \le R\}$.
--
--   This is the outer radius in the LEMMA's proof.
--
--   **Formalization Note** $\mathbb R^{n+1}$ is `EuclideanSpace ℝ (Fin (n+1))`, so $|\cdot|$ is the Euclidean norm; the ball is the full closed ball of $\mathbb R^{n+1}$ (since $T_c$ lies in the hyperplane, this is the same as the ball inside the hyperplane).
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §2, p. 544 (proof of the LEMMA): 'It follows that T_c ⊂ B(p, R), where R is the distance of p to the above point: R² = …'

import Mathlib
import Definitions.Def_LenstraIP_Rounding_SimplexData

namespace LenstraIP.Rounding

theorem modelT_subset_ball {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 1 ≤ c) :
    dist (pM n) (modelPt n c) ^ 2 =
        (if Even n then (n : ℝ) * c ^ 2 + (n : ℝ) / ((n : ℝ) + 1)
         else ((n : ℝ) + 1) * c ^ 2 - 2 * c + (n : ℝ) / ((n : ℝ) + 1)) ∧
      modelT n c ⊆ Metric.closedBall (pM n) (dist (pM n) (modelPt n c)) := by sorry

end LenstraIP.Rounding
