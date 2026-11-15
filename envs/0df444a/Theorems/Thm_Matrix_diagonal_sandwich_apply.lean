-- Prove2me | Theorems.Thm_Matrix_diagonal_sandwich_apply
-- name    : Matrix.diagonal_sandwich_apply
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-15T00:18:39.71559+00:00
-- url     : https://prove2.me/theorems/28d4b370-25d0-4f9e-8a3b-a2359556e72a
-- title:
--   Entrywise formula for a diagonal matrix sandwich
-- statement:
--   Let $D$ be a diagonal complex matrix and $A$ any square complex matrix on a finite index set. Then the $(y,z)$ entry of $DAD$ is $D_{y,y}A_{y,z}D_{z,z}$. Both matrix-product sums collapse because all off-diagonal entries of $D$ vanish.
-- source:
--   Standard finite-dimensional matrix multiplication identity; used for Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, Eq. (48).

import Mathlib

namespace Matrix

/-- Multiplication on both sides by a diagonal matrix scales an entry by the two corresponding diagonal entries. -/
theorem diagonal_sandwich_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D A : Matrix ι ι ℂ)
    (hD : ∀ x y, x ≠ y → D x y = 0) (y z : ι) :
    (D * A * D) y z = D y y * A y z * D z z := by sorry

end Matrix
