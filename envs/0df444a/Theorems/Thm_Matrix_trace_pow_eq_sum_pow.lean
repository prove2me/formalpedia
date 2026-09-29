-- Prove2me | Theorems.Thm_Matrix_trace_pow_eq_sum_pow
-- name    : Matrix.trace_pow_eq_sum_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/84656216-3e71-5f9e-abf2-62013fb868b1
-- title:
--   Trace of powers of a 2×2 matrix as a power sum
-- statement:
--   Let $R$ be a commutative ring, let $M$ be a $2\times 2$ matrix over $R$ (indexed by `Fin 2`), and let $\alpha,\beta \in R$. Assume that the trace of $M$ equals $\alpha+\beta$ and that the determinant of $M$ equals $\alpha\beta$; note that $\alpha$ and $\beta$ are merely elements of $R$ subject to these two identities, no factorisation of the characteristic polynomial over $R$ or invertibility being required. Then for every natural number $k$, the trace of $M^k$ equals $\alpha^k+\beta^k$. In particular, for $k=0$ the assertion is that the trace of the $2\times 2$ identity matrix is $2$, and for $k=1$ it is the hypothesis on the trace of $M$.
--
--   This is Newton's power-sum identity in the $2\times 2$ case: the trace of $M^k$ is determined by the trace and determinant of $M$ through the elementary symmetric functions of the pair $(\alpha,\beta)$. It serves as the computational ingredient of [`Matrix.hasDistinctRationalEigenvalues_pow`](thm.html#Matrix.hasDistinctRationalEigenvalues_pow), used in the analysis of Taylor–Wiles primes, where traces and determinants of Frobenius elements are the available data about a two-dimensional representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_trace_pow_eq_sum_pow.lean

import Definitions.Def_TaylorWiles_Primes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.trace_pow_eq_sum_pow {R : Type*} [CommRing R]
    {M : Matrix (Fin 2) (Fin 2) R} {α β : R}
    (htr : M.trace = α + β) (hdet : M.det = α * β) (k : ℕ) :
    (M ^ k).trace = α ^ k + β ^ k := by sorry
