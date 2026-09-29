-- Prove2me | Theorems.Thm_MvPolynomial_exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval
-- name    : MvPolynomial.exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/f04e3839-f63c-516f-8c7a-af99f34e5d93
-- title:
--   Scaling rigidity forcing P = c (X₀+X₁)^g
-- statement:
--   Let $g$ and $n$ be natural numbers with $n \ge 2$, and let $\alpha,\beta$ be natural numbers satisfying $\alpha + \beta = n^{2}$ and $\alpha = \beta + n$ (so $\alpha = (n^{2}+n)/2$ and $\beta = (n^{2}-n)/2$). Let $P$ be a polynomial in two variables $X_0, X_1$ over $\mathbb{Q}$, indexed by `Fin 2`, whose total degree is at most $g$. Assume that for all natural numbers $a, b$ the value of $P$ at the point whose coordinates are the rational numbers obtained by casting the naturals $\alpha a + \beta b$ and $\beta a + \alpha b$ equals $n^{2g}$ times the value of $P$ at the point with coordinates the casts of $a$ and $b$; that is, $P(\alpha a + \beta b,\ \beta a + \alpha b) = n^{2g}\,P(a,b)$ for all $(a,b) \in \mathbb{N}^{2}$. The conclusion is that there exists a rational constant $c$ with $P = c\,(X_0 + X_1)^{g}$ as an identity of polynomials, the constant being realised through the constant-polynomial embedding `MvPolynomial.C`.
--
--   This is the elementary polynomial input to Riemann–Roch for the powers of a line bundle on an abelian variety of dimension $g$: in the coordinates $X_0 + X_1$ and $X_0 - X_1$ the substitution becomes $(u,v) \mapsto (n^{2}u, nv)$, so the scaling relation together with the degree bound pins down the monomial support. It is used in the computation of Euler characteristics of tensor powers, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_forall_eulerChar_tensorPow_eq_mul_pow`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_forall_eulerChar_tensorPow_eq_mul_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvPolynomial.exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval
    (g n : ℕ) (hn : 2 ≤ n) (α β : ℕ) (hαβ : α + β = n ^ 2) (hα : α = β + n)
    (P : MvPolynomial (Fin 2) ℚ) (hP : P.totalDegree ≤ g)
    (h : ∀ a b : ℕ,
      MvPolynomial.eval ![((α * a + β * b : ℕ) : ℚ), ((β * a + α * b : ℕ) : ℚ)] P =
        (n : ℚ) ^ (2 * g) * MvPolynomial.eval ![(a : ℚ), (b : ℚ)] P) :
    ∃ c : ℚ, P = MvPolynomial.C c * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ g := by sorry
