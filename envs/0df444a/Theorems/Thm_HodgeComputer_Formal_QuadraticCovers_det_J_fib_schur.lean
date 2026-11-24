-- Prove2me | Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_det_J_fib_schur
-- name    : HodgeComputer.Formal.QuadraticCovers.det_J_fib_schur
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:32:23.462858+00:00
-- url     : https://prove2.me/theorems/e02078c8-074c-4d5e-923c-04adf615c417
-- title:
--   $4 \times 4$ Schur-complement determinant factorization for fiber Jacobians
-- statement:
--   Let $R$ be a commutative ring and $M \in \operatorname{Mat}_{4 \times 4}(R)$ a matrix whose top row satisfies $M_{00} = M_{01} = 0$. Suppose scalars $a', b', v', \dot{E}_3 \in R$ satisfy
--
--   $$M \begin{pmatrix} a' \\ b' \\ 1 \\ v' \end{pmatrix} = \begin{pmatrix} 0 \\ 0 \\ 0 \\ \dot{E}_3 \end{pmatrix}.$$
--
--   Then
--
--   $$\det(M) = M_{03} \,(M_{11} M_{20} - M_{10} M_{21})\, \dot{E}_3.$$
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/QuadraticCovers/RationalCoverResidues.lean#L21-L82

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
set_option autoImplicit false

theorem HodgeComputer.Formal.QuadraticCovers.det_J_fib_schur
    {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R)
    (a' b' v' E3_dot : R)
    (h00 : M 0 0 = 0) (h01 : M 0 1 = 0)
    (h0 : M 0 2 + M 0 3 * v' = 0)
    (h1 : M 1 0 * a' + M 1 1 * b' + M 1 2 + M 1 3 * v' = 0)
    (h2 : M 2 0 * a' + M 2 1 * b' + M 2 2 + M 2 3 * v' = 0)
    (h3 : M 3 0 * a' + M 3 1 * b' + M 3 2 + M 3 3 * v' = E3_dot) :
    M.det = M 0 3 * (M 1 1 * M 2 0 - M 1 0 * M 2 1) * E3_dot := by sorry
