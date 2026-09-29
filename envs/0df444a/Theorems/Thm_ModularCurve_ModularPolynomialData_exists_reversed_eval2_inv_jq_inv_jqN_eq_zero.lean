-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_exists_reversed_eval2_inv_jq_inv_jqN_eq_zero
-- name    : ModularCurve.ModularPolynomialData.exists_reversed_eval2_inv_jq_inv_jqN_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/3429f02e-ae4b-5cea-ac34-cfe81f45ea84
-- title:
--   The reversed modular polynomial at prime level
-- statement:
--   Let $p$ be a prime and let `data` be a `ModularPolynomialData p`, that is, a bivariate polynomial $\Phi =$ `data.Φ` in $\mathbb{Z}[X][Y]$ which is monic as a polynomial in $Y$, has $Y$-degree $\psi(p) = \sum_{d \mid p,\ d \text{ squarefree}} p/d$, and satisfies $\Phi(j(q), j(q^p)) = 0$ in the Laurent series field $\mathbb{Q}((q))$, where $X$ is evaluated at the Laurent series `jq` $= q^{-1}\cdot(\text{the } q\text{-series } j\text{Num over } \mathbb{Q})$ and $Y$ at `jqN p`, the image of `jq` under the substitution $q \mapsto q^p$ (multiplication by $p$ on exponents). Then there exists $\Psi \in \mathbb{Z}[X][Y]$ such that: for all $i, j$, the coefficient of $Y^i X^j$ in $\Psi$ equals the coefficient of $Y^{p+1-i} X^{p+1-j}$ in $\Phi$ when $i \le p+1$ and $j \le p+1$, and is $0$ otherwise; the $Y$-degree of $\Psi$ is exactly $p+1$; the constant term of its leading $Y$-coefficient is $1$; its $Y$-constant coefficient is $X^{p+1}$; $\Psi$ is invariant under the ring homomorphism `swapBivar` interchanging the two variables; and $\Psi$ vanishes at $X =$ `jq`$^{-1}$, $Y =$ (`jqN p`)$^{-1}$.
--
--   This is the reversal $\Psi_p(U,V) = U^{p+1}V^{p+1}\Phi_p(1/U,1/V)$ of the classical modular polynomial of prime level $p$, recorded together with the symmetry and monicity properties of $\Phi_p$ that make it again a symmetric polynomial of degree $p+1$ in each variable with prescribed extreme coefficients. It is used to prove integrality of $1/$`jq` times the inverse of the Atkin–Lehner image, in [`ModularCurve.exists_isIntegral_adjoin_inv_jq_mul_inv_atkinLehnerInvolutionFull`](thm.html#ModularCurve.exists_isIntegral_adjoin_inv_jq_mul_inv_atkinLehnerInvolutionFull).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_exists_reversed_eval2_inv_jq_inv_jqN_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Polynomial

theorem ModularCurve.ModularPolynomialData.exists_reversed_eval2_inv_jq_inv_jqN_eq_zero
    (p : ℕ) [Fact p.Prime] (data : ModularPolynomialData p) :
    ∃ Ψ : Polynomial (Polynomial ℤ),
      (∀ i j : ℕ, (Ψ.coeff i).coeff j =
        if i ≤ p + 1 ∧ j ≤ p + 1 then (data.Φ.coeff (p + 1 - i)).coeff (p + 1 - j) else 0) ∧
      Ψ.natDegree = p + 1 ∧
      (Ψ.coeff (p + 1)).coeff 0 = 1 ∧
      Ψ.coeff 0 = X ^ (p + 1) ∧
      swapBivar Ψ = Ψ ∧
      Ψ.eval₂ (Polynomial.aeval (R := ℤ) jq⁻¹).toRingHom (jqN p)⁻¹ = 0 := by sorry
