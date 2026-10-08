-- Prove2me | Theorems.Thm_LenstraIP_Rounding_rounding_ratio_le
-- name    : LenstraIP.Rounding.rounding_ratio_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:06:02.483313+00:00
-- url     : https://prove2.me/theorems/5acb7f67-0477-4c06-b7c4-5851d2c85fd6
-- title:
--   §2, p. 543 — if the simplex v₀,…,vₙ ⊂ K satisfies (16) and τ makes it regular, then B(p,r) ⊂ τK ⊂ B(p,R) with R/r ≤ 2n^{3/2}
-- statement:
--   Let $n \ge 1$ and let $K \subseteq \mathbb R^n$ be a convex set. Let $v_0, v_1, \dots, v_n \in K$ be points with $v_1 - v_0, \dots, v_n - v_0$ linearly independent, and let $g_0, g_1, \dots, g_n : \mathbb R^n \to \mathbb R$ be linear functions such that, for $i = 0, 1, \dots, n$,
--   $$g_i \text{ is constant on } \{v_j : 0 \le j \le n,\ j \ne i\}, \qquad g_i(v_i) \ne g_i(v_j) \ \text{ for } 0 \le j \le n,\ j \ne i. \tag{15}$$
--   Assume the stopping condition of the second stage of the algorithm:
--   $$|g_i(x - v_j)| \le \tfrac32\, |g_i(v_i - v_j)| \quad \text{for all } x \in K \text{ and all } i, j \in \{0, 1, \dots, n\} \text{ with } i \ne j. \tag{16}$$
--   Let $\tau$ be a nonsingular endomorphism of $\mathbb R^n$ such that $\tau(v_0), \tau(v_1), \dots, \tau(v_n)$ span a regular $n$-simplex, and let $p = (n+1)^{-1}\sum_{j=0}^n \tau(v_j)$. Then there are positive real numbers $r, R$ with
--   $$B(p, r) \subseteq \tau K \subseteq B(p, R), \qquad \frac{R}{r} \le 2n^{3/2},$$
--   where $B(p, \rho) = \{x \in \mathbb R^n : |x - p| \le \rho\}$ is the closed Euclidean ball.
--
--   These are conditions (3) and (4) of §1 with $c_1 = 2n^{3/2}$: the second geometric ingredient of Lenstra's algorithm, which turns the simplex found by the volume-increasing procedure into a coordinate change under which $K$ is "round".
--
--   **Formalization Note** The paper's $K = \{x : Ax \le b\}$ is a bounded polyhedron and the $v_j$ are vertices of $K$; the claim uses only that $K$ is convex and contains the $v_j$ (Remark (d) on p. 545 applies the algorithm to any compact convex body), so it is stated for any convex $K$ and any points $v_j \in K$. Boundedness of $K$ is not assumed: it follows from (16). $\tau$ is a linear equivalence (`≃ₗ[ℝ]`), and "span a regular $n$-simplex" means all pairwise distances $|\tau(v_i) - \tau(v_j)|$, $i \ne j$, are equal and positive. "Certain positive real numbers $r, R$" is an existential with $0 < r$ and $0 < R$. $n \ge 1$ is assumed. $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $n^{3/2}$ is the real power.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §2, p. 543: 'With p = (n + 1)⁻¹ Σ_{j=0}^n τ(vⱼ) we now claim that B(p, r) ⊂ τK ⊂ B(p, R) for certain positive real numbers r, R satisfying R/r ≤ 2n^{3/2}'; (15) pp. 542–543, (16) p. 543

import Mathlib
import Definitions.Def_LenstraIP_Rounding_SimplexData

namespace LenstraIP.Rounding

theorem rounding_ratio_le {n : ℕ} (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : Convex ℝ K)
    (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) (hv : AffineIndependent ℝ v)
    (hvK : ∀ j, v j ∈ K)
    (g : Fin (n + 1) → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ))
    (hg_const : ∀ i j k, j ≠ i → k ≠ i → g i (v j) = g i (v k))
    (hg_ne : ∀ i j, j ≠ i → g i (v i) ≠ g i (v j))
    (h16 : ∀ x ∈ K, ∀ i j, i ≠ j → |g i (x - v j)| ≤ 3 / 2 * |g i (v i - v j)|)
    (τ : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hτ : IsRegular (τ ∘ v)) :
    ∃ r R : ℝ, 0 < r ∧ 0 < R ∧
      Metric.closedBall (centroid (τ ∘ v)) r ⊆ τ '' K ∧
      τ '' K ⊆ Metric.closedBall (centroid (τ ∘ v)) R ∧
      R / r ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 2) := by sorry

end LenstraIP.Rounding
