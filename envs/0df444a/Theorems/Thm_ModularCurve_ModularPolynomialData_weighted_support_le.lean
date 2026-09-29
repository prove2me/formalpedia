-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_weighted_support_le
-- name    : ModularCurve.ModularPolynomialData.weighted_support_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/b77cb841-9909-5dcb-a9e8-44afa9f3d2e7
-- title:
--   Weighted support bounds for the level-p modular polynomial
-- statement:
--   Let $p$ be a prime and let `data` be a modular-polynomial datum at level $p$, that is, a polynomial $\Phi =$ `data.Φ` in $\mathbb{Z}[X][X]$ (a polynomial in an outer variable whose coefficients are polynomials in an inner variable) which is monic in the outer variable, whose degree in the outer variable equals $\psi(p) = \sum_{d \mid p,\ d \text{ squarefree}} p/d = p+1$, and which satisfies $\Phi = 0$ after evaluation via `eval₂` of the inner variable at $j(q)$ (the ring homomorphism `evalAtJ`, i.e. $\mathbb{Z}[X] \to \mathbb{Q}((q))$ sending the variable to the Laurent series $j(q)$) and of the outer variable at $j(q^p)$ (the series `jqN p`). The conclusion is the conjunction of two statements about the bihomogeneous support of $\Phi$ after removal of two monomials. First: for all $b, a \in \mathbb{N}$, if the coefficient of the inner $X^a$ inside the $b$-th outer coefficient of $\Phi - \bigl(X^{p+1} - C(X^p)\,X^p\bigr)$ is nonzero, then $1\cdot a + p\cdot b \le p^2 + p - 1$. Second: for all $b, a \in \mathbb{N}$, if the corresponding coefficient of $\Phi - \bigl(C(X^{p+1}) - C(X^p)\,X^p\bigr)$ is nonzero, then $p\cdot a + 1\cdot b \le p^2 + p - 1$. Here $C$ is the inclusion of the inner polynomial ring as constants in the outer variable, so that in the first binomial the subtracted monomials are $Y^{p+1}$ and $-X^pY^p$, and in the second $X^{p+1}$ and $-X^pY^p$, writing $X$ for the inner and $Y$ for the outer variable.
--
--   These are the two extreme edges of the Newton polygon of the modular equation $\Phi_p$ at the two cusps: in the weighting $(1,p)$ attached to $q \mapsto (j(q), j(q^p))$ the monomials of maximal weight $p^2+p$ are exactly $Y^{p+1}$ and $-X^pY^p$, and symmetrically for the transposed weighting $(p,1)$. The bounds are used in the construction of the cusp charts on $X_0(p)$, in particular in the uniqueness of the places attached to the charts at $(\infty,0)$ and $(0,\infty)$ and in the analysis of the associated Igusa-type scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_weighted_support_le.lean

import Definitions.Def_ModularCurve_FibrePoly

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve Polynomial

theorem ModularCurve.ModularPolynomialData.weighted_support_le (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) :
    (∀ b a : ℕ, ((data.Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
        1 * a + p * b ≤ p ^ 2 + p - 1) ∧
      (∀ b a : ℕ, ((data.Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
        p * a + 1 * b ≤ p ^ 2 + p - 1) := by sorry
