-- Prove2me | Theorems.Thm_ModernConvex_Ellipsoids_det_sym_add_skew
-- name    : ModernConvex.Ellipsoids.det_sym_add_skew
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:12.775733+00:00
-- url     : https://prove2.me/theorems/8f0e0704-e205-4ea8-9978-74bb051bf8fb
-- title:
--   Lemma 4.9.1 — S ≻ 0 symmetric, C skew-symmetric: |Det(S + C)| ≥ Det(S)
-- statement:
--   Let $Y=S+C$ be a square real $n\times n$ matrix written as the sum of a symmetric matrix $S$ and a skew-symmetric matrix $C$ ($C^T=-C$). Assume that $S$ is positive definite. Then
--   $$|\operatorname{Det}(Y)|\ge\operatorname{Det}(S).$$
--
--   The determinant of the symmetric part therefore bounds from below the volume $|\operatorname{Det}(\sum_iA_iX_i)|$ of the inner ellipsoids of Proposition 4.9.6. This lets one maximize a concave function of the symmetric part instead of the determinant of a general square matrix.
--
--   **Formalization Note** "Symmetric and positive definite" is Mathlib's `PosDef`, which includes symmetry.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 273, Lemma 4.9.1

import Mathlib

open Matrix

namespace ModernConvex.Ellipsoids

/-- Ben-Tal–Nemirovski, Lemma 4.9.1, p. 273. Let `Y = S + C` be a square matrix represented as the
sum of a symmetric matrix `S` and a skew-symmetric (`Cᵀ = −C`) matrix `C`. Assume that `S` is
positive definite. Then `|Det(Y)| ≥ Det(S)`. -/
theorem det_sym_add_skew {n : ℕ} (S C : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (hC : Cᵀ = -C) :
    S.det ≤ |(S + C).det| := by sorry

end ModernConvex.Ellipsoids
