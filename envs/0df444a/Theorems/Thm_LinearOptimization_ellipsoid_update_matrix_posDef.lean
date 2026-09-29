-- Prove2me | Theorems.Thm_LinearOptimization_ellipsoid_update_matrix_posDef
-- name    : LinearOptimization.ellipsoid_update_matrix_posDef
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-09T17:04:53.936629+00:00
-- url     : https://prove2.me/theorems/2950fb25-a640-40dc-a906-a12b33a9370d
-- title:
--   Positive definiteness of the ellipsoid update matrix
-- statement:
--   Let $n \ge 2$, let $D$ be a symmetric positive-definite $n \times n$ real matrix, and let $a \in \mathbb R^n$ be nonzero. Define
--
--   $$
--   \bar D=\frac{n^2}{n^2-1}\left(D-\frac{2}{n+1}\frac{Daa^{\mathsf T}D}{a^{\mathsf T}Da}\right).
--   $$
--
--   Then $\bar D$ is positive definite.
--
--   This is the positive-definiteness component of the ellipsoid update in Theorem 8.1 and guarantees that the updated quadratic set is again an ellipsoid.
--
--   **Formalization Note** The matrix $Daa^{\mathsf T}D$ is represented by `D * vecMulVec a a * D`.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 8.1, p. 366, proof in Section 8.2, pp. 366–369

import Definitions.Def_LinearOptimization_EllipsoidMethod

open Matrix

theorem LinearOptimization.ellipsoid_update_matrix_posDef {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (ellipsoidUpdateMatrix D a).PosDef := by
  sorry
