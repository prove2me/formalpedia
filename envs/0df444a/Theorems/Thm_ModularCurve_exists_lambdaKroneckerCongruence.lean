-- Prove2me | Theorems.Thm_ModularCurve_exists_lambdaKroneckerCongruence
-- name    : ModularCurve.exists_lambdaKroneckerCongruence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/03695227-d60a-5fde-aacd-719531f5ab54
-- title:
--   Existence of a λ-modular polynomial with Kronecker's congruence
-- statement:
--   Let $q$ be a prime with $q \neq 2$. The assertion is that there exists a term `data` of the structure `LambdaModularPolynomialData q`, that is, a bivariate polynomial $\Psi =$ `data.Ψ` in `Polynomial (Polynomial ℤ)` — a polynomial in an outer variable $X$ with coefficients in $\mathbb{Z}[\mu]$ — which is monic, has degree exactly $q+1$ in $X$, and vanishes under the following substitution: each coefficient in $\mathbb{Z}[\mu]$ is evaluated at the Laurent series `lambdaInt` by the ring homomorphism `evalAtLambdaInt` and pushed into Laurent series over $\mathbb{Q}$ along `laurentMap (Int.castRingHom ℚ)`, while the outer variable $X$ is sent to `lambdaNModC ℚ q`, the series `qExpand ℚ q (lambdaModC ℚ)`; the resulting Laurent series over $\mathbb{Q}$ is $0$. Moreover this $\Psi$ may be chosen so that its reduction modulo $q$, applied to all coefficients at both levels by `reduceModBivar q`, satisfies in $(\mathbb{Z}/q)[\mu][X]$ the identity $$\mathrm{red}_q(\Psi) = (\mu^{q} - X)\,(\mu - X^{q}),$$ where $\mu$ denotes the inner variable viewed as a constant, i.e. `Polynomial.C Polynomial.X`.
--
--   This is the Kronecker congruence for the modular equation attached to the $\lambda$-coordinate (level two), packaged together with the existence of the modular polynomial itself. It is the input to the local study of the $\lambda$-modular curve at a node: the statements about maximal ideals, level-two values and the identification of the adic completion of the localisation with a $uv$-crossing model all invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_lambdaKroneckerCongruence.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_KroneckerTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_lambdaKroneckerCongruence (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    ∃ data : LambdaModularPolynomialData q, reduceModBivar q data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by sorry
