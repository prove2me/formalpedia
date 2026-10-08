-- Prove2me | Theorems.Thm_LenstraIP_Rounding_cond16_iff_subset_T
-- name    : LenstraIP.Rounding.cond16_iff_subset_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:05:41.298657+00:00
-- url     : https://prove2.me/theorems/df330a77-6ad9-4142-bc82-7a3f321a58c3
-- title:
--   §2, p. 543 — condition (16) for all x ∈ K and i ≠ j means precisely that τK ⊂ T_{3/2}
-- statement:
--   Let $n \ge 1$, let $K \subseteq \mathbb R^n$ be any set, and let $v_0, v_1, \dots, v_n \in \mathbb R^n$ be points with $v_1 - v_0, \dots, v_n - v_0$ linearly independent. Let $g_0, g_1, \dots, g_n : \mathbb R^n \to \mathbb R$ be linear functions satisfying (15):
--   $$g_i \text{ is constant on } \{v_j : 0 \le j \le n,\ j \ne i\}, \qquad g_i(v_i) \ne g_i(v_j) \ \text{ for } 0 \le j \le n,\ j \ne i,$$
--   for $i = 0, 1, \dots, n$. Let $\tau$ be a nonsingular linear endomorphism of $\mathbb R^n$, write $z_j = \tau(v_j)$, and let $T_{3/2}$ be the set of points $x$ for which replacing any one vertex $z_i$ of the simplex $z_0, \dots, z_n$ by $x$ gives a simplex of volume at most $\tfrac32\,\mathrm{vol}(z_0, \dots, z_n)$. Then condition (16),
--   $$|g_i(x - v_j)| \le \tfrac32\, |g_i(v_i - v_j)| \quad \text{for all } x \in K \text{ and all } i, j \in \{0, 1, \dots, n\} \text{ with } i \ne j,$$
--   holds if and only if $\tau K \subseteq T_{3/2}$.
--
--   The identity behind it is stated on the same page: replacing $v_i$ by $x$ "enlarges $\mathrm{vol}(v_0, v_1, \dots, v_n)$ by a factor $|g_i(x - v_j)|/|g_i(v_i - v_j)|$ (for $j \ne i$)", and $\tau$ multiplies all volumes by the same factor $|\det\tau|$. This is how the stopping rule (16) of the second stage of the algorithm is translated into the geometric statement used by the LEMMA.
--
--   **Formalization Note** The paper's $v_j$ are vertices of the polytope $K$; the equivalence holds for any set $K$ and any points $v_j$, which is the generality stated here. Affine independence (`AffineIndependent ℝ v`) is the paper's "$v_1 - v_0, \dots, v_n - v_0$ linearly independent". The first clause of (15) is written as $g_i(v_j) = g_i(v_k)$ for all $j, k \ne i$. $n \ge 1$ is assumed (for $n = 0$ there is no pair $i \ne j$). $\tau$ is a linear equivalence (`≃ₗ[ℝ]`).
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §2, p. 543: 'Condition (16) (for all x ∈ K and all i ≠ j) means precisely that τK ⊂ T_{3/2}'; (15) on pp. 542–543, (16) on p. 543

import Mathlib
import Definitions.Def_LenstraIP_Rounding_SimplexData

namespace LenstraIP.Rounding

theorem cond16_iff_subset_T {n : ℕ} (hn : 1 ≤ n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) (hv : AffineIndependent ℝ v)
    (g : Fin (n + 1) → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ))
    (hg_const : ∀ i j k, j ≠ i → k ≠ i → g i (v j) = g i (v k))
    (hg_ne : ∀ i j, j ≠ i → g i (v i) ≠ g i (v j))
    (τ : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (∀ x ∈ K, ∀ i j, i ≠ j → |g i (x - v j)| ≤ 3 / 2 * |g i (v i - v j)|) ↔
      τ '' K ⊆ Tset (3 / 2) (τ ∘ v) := by sorry

end LenstraIP.Rounding
