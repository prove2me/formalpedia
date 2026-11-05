-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_vecFin_dotProduct
-- name    : ModernConvex.Relaxations.vecFin_dotProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:40:45.815062+00:00
-- url     : https://prove2.me/theorems/23a9a114-b73f-4b7d-8fe2-926a3b106228
-- title:
--   The vector dot product is the Frobenius pairing of symmetric matrices
-- statement:
--   For real symmetric $n\times n$ matrices $A,B$ enumerated column by column as vectors of length $n^2$ (the reindexing of `ModernConvex_MatrixVec`), the coordinate dot product of the two vectors equals the Frobenius pairing
--   $$\texttt{vecFin}\,A\cdot\texttt{vecFin}\,B=\sum_{i,j}A_{ij}B_{ij}.$$
--   This follows from Mathlib's $\texttt{vec}\,A\cdot\texttt{vec}\,B=(A^{\mathsf T}B).\mathrm{trace}$ together with the symmetry of $A$ and $B$, and it is what identifies the ambient inner product of the ellipsoid method with the pairing used to separate matrices from the positive semidefinite cone.
-- source:
--   Mathlib's Matrix.vec_dotProduct_vec combined with symmetry; reindexing of Def_ModernConvex_MatrixVec.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_MatrixVec

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- The coordinate dot product of the enumerated vectors is the Frobenius pairing. -/
theorem vecFin_dotProduct {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    vecFin A ⬝ᵥ vecFin B = ∑ i, ∑ j, A i j * B i j := by sorry

end ModernConvex.Relaxations
