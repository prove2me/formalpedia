-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one
-- name    : Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/c8bce8b0-edd5-5602-b497-0ee5560f503b
-- title:
--   Primitive upper-triangular matrices of determinant N in one double coset
-- statement:
--   Let $N,a,b,d$ be natural numbers such that $N \neq 0$, $a d = N$, and $\gcd(a,\gcd(b,d)) = 1$. Then there exist $\gamma_1,\gamma_2 \in \mathrm{SL}_2(\mathbb{Z})$, i.e. elements of `Matrix.SpecialLinearGroup (Fin 2) ℤ`, such that, after casting $a,b,d,N$ into $\mathbb{Z}$ and coercing $\gamma_1,\gamma_2$ to their underlying $2 \times 2$ integer matrices, the equality of matrices in `Matrix (Fin 2) (Fin 2) ℤ`
--   $$\begin{pmatrix} a & b \\ 0 & d\end{pmatrix} \;=\; \gamma_1 \begin{pmatrix} N & 0 \\ 0 & 1\end{pmatrix} \gamma_2$$
--   holds. Thus a primitive upper-triangular integer matrix with non-negative entries and determinant $N > 0$ lies in the double coset $\mathrm{SL}_2(\mathbb{Z}) \, \mathrm{diag}(N,1) \, \mathrm{SL}_2(\mathbb{Z})$. Note that the usual normalisation $0 \le b < d$ of coset representatives is not assumed, only the coprimality condition; the entries are natural numbers rather than arbitrary integers; and the orientation of the factorisation is with $\mathrm{diag}(N,1)$ (not $\mathrm{diag}(1,N)$) in the middle.
--
--   This is the $\mathrm{SL}_2$ refinement of the elementary-divisor (Smith) normal form in rank two: the elementary divisors of a primitive integer matrix of determinant $N$ are $1$ and $N$, and the reduction can be carried out on both sides inside $\mathrm{SL}_2(\mathbb{Z})$ rather than $\mathrm{GL}_2(\mathbb{Z})$. It is used in the study of the modular equation, where a level-one modular function is evaluated along the cosets $\mathrm{SL}_2(\mathbb{Z})\binom{a\;b}{0\;d}$ with $ad = N$; it is cited by [`ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero`](thm.html#ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one
    {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
    ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by sorry
