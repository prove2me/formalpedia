-- Prove2me | Theorems.Thm_ModularCurve_deuringPolynomial_sq_mul_thetaL_lambda_pow
-- name    : ModularCurve.deuringPolynomial_sq_mul_thetaL_lambda_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/1ab12328-1845-5ce6-9e83-1b7b4a14f6d8
-- title:
--   H_q(16λ)² (θλ)^{q-1}=(λ(1-16λ))^{q-1} in characteristic q
-- statement:
--   Let $q$ be a prime with $5 \le q$, and let $k$ be a field of characteristic $q$. Two ingredients enter. First, $\lambda$-series: `lambdaInt` is the integral Laurent series $t \cdot \mathrm{etaProd}^{8} \cdot (\mathrm{etaProd}^{16})[4] \cdot (\mathrm{dedekindEtaUnitInv})[2]$, where $t$ denotes the Laurent monomial `HahnSeries.single 1 1`, power series are viewed as Laurent series, and $[\,m\,]$ denotes the substitution operator `qExpand` of index $m$; `lambdaModC k` is its image under coefficientwise reduction along the ring homomorphism $\mathbb{Z} \to k$, a Laurent series over $k$, written $\bar\lambda$ below. Second, the Deuring polynomial $\mathrm{deuringPolynomial}\ q = \sum_{i=0}^{(q-1)/2} \binom{(q-1)/2}{i}^{2} X^{i} \in \mathbb{Z}[X]$, reduced mod $q$ and evaluated at $16\bar\lambda$. Finally, $\theta$ is the $k$-linear operator `thetaL k` on Laurent series over $k$ sending $f$ to $t \cdot f'$, with $f'$ the formal derivative. The assertion is the identity of Laurent series over $k$
--   $$\bigl(H_q(16\bar\lambda)\bigr)^{2} \cdot \bigl(\theta\bar\lambda\bigr)^{q-1} \;=\; \bigl(\bar\lambda\,(1 - 16\bar\lambda)\bigr)^{q-1},$$
--   where $H_q$ is the reduction of the Deuring polynomial and the exponent $q-1$ is the natural-number difference.
--
--   This is the level-two form, in characteristic $q$, of the classical relation between the Deuring–Hasse supersingular polynomial and the logarithmic derivative of the modular $\lambda$-function: it is a sixth root of the identity obtained by combining the level-two relation [`ModularCurve.delta_pow_mul_deuringPolynomial_lambda_pow_twelve`](thm.html#ModularCurve.delta_pow_mul_deuringPolynomial_lambda_pow_twelve) with Jacobi's formula $(\theta\lambda)^{6} = \lambda^{4}(1-16\lambda)^{4}\Delta[2]$, the normalisation being fixed by $H_q(0) = 1$. It expresses $(\theta\bar\lambda)^{q-1}$ as a rational function of $\bar\lambda$ with double poles at the supersingular values, and is used in [`ModularCurve.lambdaKroneckerRemainder_frobeniusGraph_ode`](thm.html#ModularCurve.lambdaKroneckerRemainder_frobeniusGraph_ode).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deuringPolynomial_sq_mul_thetaL_lambda_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.deuringPolynomial_sq_mul_thetaL_lambda_pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    (Polynomial.aeval (16 * lambdaModC k) ((Polynomial.deuringPolynomial q).map (Int.castRingHom k))) ^ 2 * thetaL k (lambdaModC k) ^ (q - 1)
      = (lambdaModC k * (1 - 16 * lambdaModC k)) ^ (q - 1) := by sorry
