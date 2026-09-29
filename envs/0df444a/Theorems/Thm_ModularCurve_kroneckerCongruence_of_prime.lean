-- Prove2me | Theorems.Thm_ModularCurve_kroneckerCongruence_of_prime
-- name    : ModularCurve.kroneckerCongruence_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/5e172b8c-c42d-529e-96a3-7781a2f2b31b
-- title:
--   Kronecker's congruence for modular polynomials of prime level
-- statement:
--   Let $\ell$ be a prime and let `data` be any term of [`ModularCurve.ModularPolynomialData ℓ`](def/ModularCurve_X0.html#L215), that is, a polynomial $\Phi =$ `data.Φ` in $\mathbb{Z}[X][Y]$ (a polynomial in the outer variable $Y$ with coefficients in $\mathbb{Z}[X]$) which is monic, whose degree in $Y$ equals `dedekindPsi ℓ` $= \sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$ (so $\ell+1$ for $\ell$ prime), and which satisfies $\Phi = 0$ after substituting, via the ring homomorphism `evalAtJ` sending $X$ to the $q$-expansion $j(q)$ in `LaurentSeries ℚ` on coefficients, the Laurent series `jqN ℓ` for the outer variable $Y$. The conclusion is the predicate [`ModularCurve.KroneckerCongruence ℓ data`](def/ModularCurve_KroneckerTransport.html#L127): the coefficientwise reduction `reduceModBivar ℓ`, induced by $\mathbb{Z} \to \mathbb{Z}/\ell$ on the coefficients of the coefficients, carries $\Phi$ to
--   $$\left(\,(\mathrm{C}\,X)^{\ell} - Y\,\right)\left(\,\mathrm{C}\,X - Y^{\ell}\,\right)$$
--   in $(\mathbb{Z}/\ell)[X][Y]$, where $\mathrm{C}\,X$ denotes the inner variable $X$ viewed as a constant in the outer variable $Y$. Thus the assertion holds for every such $\Phi$, not merely for one distinguished choice.
--
--   This is Kronecker's congruence $\Phi_\ell(X,Y) \equiv (X^\ell - Y)(X - Y^\ell) \pmod{\ell}$ for the modular polynomial of prime level $\ell$. Stated for an arbitrary `ModularPolynomialData ℓ`, it discharges the congruence hypothesis in the results on the Frobenius and Verschiebung factors of $\Phi_\ell$ modulo $\ell$, and feeds the local analysis of $X_0(\ell)$ in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_kroneckerCongruence_of_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_KroneckerTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.kroneckerCongruence_of_prime
    (ℓ : ℕ) [Fact ℓ.Prime] (data : ModularCurve.ModularPolynomialData ℓ) :
    ModularCurve.KroneckerCongruence ℓ data := by sorry
