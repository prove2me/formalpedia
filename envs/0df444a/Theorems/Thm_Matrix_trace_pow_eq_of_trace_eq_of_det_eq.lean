-- Prove2me | Theorems.Thm_Matrix_trace_pow_eq_of_trace_eq_of_det_eq
-- name    : Matrix.trace_pow_eq_of_trace_eq_of_det_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/539a799f-c99c-5f6c-b6de-cfa7f80f2e15
-- title:
--   Equal trace and determinant give equal traces of all powers
-- statement:
--   Let $R$ be a commutative ring and let $M, N$ be $2\times 2$ matrices over $R$, indexed by `Fin 2`. Assume that their traces agree, $\operatorname{tr} M = \operatorname{tr} N$, and that their determinants agree, $\det M = \det N$. Then for every natural number $k$ the traces of the $k$-th powers agree: $\operatorname{tr}(M^k) = \operatorname{tr}(N^k)$. In particular the case $k = 0$ is included, where both sides equal $\operatorname{tr}(1) = 2$ in $R$, and no invertibility, finiteness or characteristic hypothesis is imposed on $R$.
--
--   This is the power-sum identity for $2\times 2$ matrices: the Newton-type recursion $t_{k+2} = (\operatorname{tr} M)\,t_{k+1} - (\det M)\,t_k$ shows that the whole sequence of power traces is determined by the characteristic polynomial. It is used in the identification of two-dimensional Galois representations by their Frobenius data, where agreement of trace and determinant at a single element is propagated to all of its powers; it is invoked by [`GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq`](thm.html#GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq) and by [`Representation.trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le`](thm.html#Representation.trace_eq_and_det_eq_of_frobenius_agree_of_ker_restrictNormalHom_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_trace_pow_eq_of_trace_eq_of_det_eq.lean

import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.trace_pow_eq_of_trace_eq_of_det_eq {R : Type*} [CommRing R]
    {M N : Matrix (Fin 2) (Fin 2) R} (htr : M.trace = N.trace) (hdet : M.det = N.det)
    (k : ℕ) : (M ^ k).trace = (N ^ k).trace := by sorry
