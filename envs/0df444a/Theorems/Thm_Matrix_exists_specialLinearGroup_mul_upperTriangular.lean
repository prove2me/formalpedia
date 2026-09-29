-- Prove2me | Theorems.Thm_Matrix_exists_specialLinearGroup_mul_upperTriangular
-- name    : Matrix.exists_specialLinearGroup_mul_upperTriangular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/f1f0f9cb-f954-52f7-9db9-db1330b404f3
-- title:
--   Hermite normal form for nonsingular integer 2×2 matrices
-- statement:
--   Let $M$ be a $2\times 2$ matrix with integer entries whose determinant is nonzero. The theorem asserts the existence of an element $B$ of $\mathrm{SL}_2(\mathbb{Z})$ (the special linear group of $2\times2$ matrices over $\mathbb{Z}$, i.e. integer matrices of determinant $1$) together with integers $a$, $b$, $d$ such that $a>0$, $0\le b$, $b<|d|$, $a d=\det M$, and $M$ equals the product of the underlying matrix of $B$ with the explicit matrix $\begin{pmatrix}a&b\\0&d\end{pmatrix}$. Note that $d$ is not required to be positive: since $ad=\det M$ and $a>0$, the sign of $d$ is that of $\det M$, and the bound on $b$ is by $|d|$ rather than by $d$; also $d\ne 0$ is implicit in $0\le b<|d|$. Thus every integer $2\times2$ matrix of nonzero determinant lies in the left $\mathrm{SL}_2(\mathbb{Z})$-orbit of a uniquely shaped upper triangular matrix with positive upper-left entry and off-diagonal entry reduced modulo the lower-right entry.
--
--   This is the row Hermite normal form for nonsingular $2\times 2$ integer matrices, giving upper triangular representatives for the left cosets $\mathrm{SL}_2(\mathbb{Z})\backslash\{M\in M_2(\mathbb{Z}):\det M=n\}$ that underlie the coset decompositions used to define the Hecke operators $T_n$. It is used in the project's work on Hecke operators on cusp forms and on relative indices of congruence subgroups, via [`ModularForm.exists_cuspForm_coeffHeckeT_eq_of_modEq_one`](thm.html#ModularForm.exists_cuspForm_coeffHeckeT_eq_of_modEq_one) and [`ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC`](thm.html#ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_specialLinearGroup_mul_upperTriangular.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.exists_specialLinearGroup_mul_upperTriangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < |d| ∧ a * d = M.det ∧ M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] := by sorry
