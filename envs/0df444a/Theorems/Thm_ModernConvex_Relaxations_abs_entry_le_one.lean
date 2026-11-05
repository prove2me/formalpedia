-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_abs_entry_le_one
-- name    : ModernConvex.Relaxations.abs_entry_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:51:10.46091+00:00
-- url     : https://prove2.me/theorems/b6fdb001-d2a0-4417-bd40-1efde5123307
-- title:
--   A unit-diagonal semidefinite matrix has entries of modulus at most one
-- statement:
--   **Boundedness of the primal body.** If $X\succeq0$ and $X_{ii}=1$ for all $i$, then every entry satisfies $|X_{ij}|\le1$.
--
--   The $2\times2$ principal submatrix on the index pair $\{i,j\}$ is positive semidefinite (a principal submatrix of a positive semidefinite matrix is positive semidefinite), so its determinant is nonnegative:
--   $$X_{ii}X_{jj}-X_{ij}X_{ji}\ge0,$$
--   and by symmetry $X_{ji}=X_{ij}$, so $X_{ij}^2\le X_{ii}X_{jj}=1$. Hence $|X_{ij}|\le1$: the body lies in the cube $[-1,1]^{n\times n}$, so it is bounded.
-- source:
--   Standard: principal submatrices of a positive semidefinite matrix are positive semidefinite (Ben-Tal & Nemirovski, p. 170); boundedness of the MAXCUT SDP body.

import Mathlib

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **Boundedness of the primal body.** A positive semidefinite matrix with unit diagonal has
`|X_ij| ≤ 1`. -/
theorem abs_entry_le_one {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (hdiag : ∀ k, X k k = 1) (i j : Fin n) : |X i j| ≤ 1 := by sorry

end ModernConvex.Relaxations
