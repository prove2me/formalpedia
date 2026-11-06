-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_eq_zero_of_posSemidef_diag_zero
-- name    : ModernConvex.Relaxations.eq_zero_of_posSemidef_diag_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:19:43.233303+00:00
-- url     : https://prove2.me/theorems/0a4a45a3-b314-4de9-9833-670439ca58ea
-- title:
--   A positive semidefinite matrix with zero diagonal is zero
-- statement:
--   **The zero-diagonal branch of the PSD oracle.**
--
--   *If $M\succeq0$ and $M_{ii}=0$ for all $i$, then $M=0$.* Indeed the $2\times2$ principal submatrix on any index pair $\{i,j\}$ is positive semidefinite, so its determinant is nonnegative:
--   $$M_{ii}M_{jj}-M_{ij}M_{ji}=-M_{ij}^2\ge0,$$
--   using symmetry — hence $M_{ij}=0$ for all $i,j$.
--
--   *Consequently,* if $M$ is symmetric, has zero diagonal, and is not zero, then $M$ is **not** positive semidefinite: there is $v$ with $v^{\mathsf T}Mv<0$.
--
--   This is the branch that makes the elimination recursion terminate. Symmetric elimination peels off one coordinate at a time via Schur complements; if the remaining block has a negative diagonal entry the certificate is a unit vector, and if its diagonal vanishes entirely then either the block is zero (and the recursion stops, having proved semidefiniteness) or it is nonzero and a certificate exists by this lemma. Both certificates are read off the entries of $M$ by comparisons and signs, so they are rational whenever $M$ is — which is what a machine-checkable certificate requires.
-- source:
--   The 2x2 principal-minor criterion for positive semidefinite matrices (Ben-Tal & Nemirovski, p. 170); base case of the symmetric-elimination PSD oracle.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **A positive semidefinite matrix with zero diagonal is zero.** -/
theorem eq_zero_of_posSemidef_diag_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (hdiag : ∀ i, M i i = 0) : M = 0 := by sorry

end ModernConvex.Relaxations
