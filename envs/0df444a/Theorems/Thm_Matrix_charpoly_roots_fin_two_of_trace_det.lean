-- Prove2me | Theorems.Thm_Matrix_charpoly_roots_fin_two_of_trace_det
-- name    : Matrix.charpoly_roots_fin_two_of_trace_det
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T16:12:35.29606+00:00
-- url     : https://prove2.me/theorems/41229ef4-2a3d-4311-b273-673b2208f1eb
-- title:
--   Eigenvalues of a $2\times2$ matrix from its trace and determinant
-- statement:
--   Let $R$ be an integral domain, $V$ a $2\times2$ matrix over $R$ and $\mu_1,\mu_2\in R$ with $\operatorname{tr}V=\mu_1+\mu_2$ and $\det V=\mu_1\mu_2$. Then the multiset of roots of the characteristic polynomial of $V$ is $\{\mu_1,\mu_2\}$, i.e. $\chi_V(X)=(X-\mu_1)(X-\mu_2)$.
-- source:
--   Standard linear algebra (Vieta's formulas for the characteristic polynomial $X^2-\operatorname{tr}V\,X+\det V$ of a $2\times2$ matrix).

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots

open Polynomial

theorem Matrix.charpoly_roots_fin_two_of_trace_det {R : Type*} [CommRing R] [IsDomain R] {V : Matrix (Fin 2) (Fin 2) R} {μ₁ μ₂ : R}
    (htr : V.trace = μ₁ + μ₂) (hdet : V.det = μ₁ * μ₂) :
    V.charpoly.roots = {μ₁, μ₂} := by sorry
