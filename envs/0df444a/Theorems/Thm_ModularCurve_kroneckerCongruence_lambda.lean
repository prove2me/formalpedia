-- Prove2me | Theorems.Thm_ModularCurve_kroneckerCongruence_lambda
-- name    : ModularCurve.kroneckerCongruence_lambda
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/c14ca404-f0a7-50a3-9f25-1e3a754b503e
-- title:
--   Kronecker congruence for the λ modular equation
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and let `data` be a term of `LambdaModularPolynomialData q`, that is: a bivariate polynomial $\Psi \in \mathbb{Z}[Y][X]$ (an element of `Polynomial (Polynomial ℤ)`, with $X$ the outer variable) which is monic in $X$, has degree $q+1$ in $X$, and vanishes when its coefficients, polynomials in $Y$, are evaluated at the integral $\lambda$-series `lambdaInt` and pushed into Laurent series over $\mathbb{Q}$, while the outer variable is set to `lambdaNModC ℚ q`, the $q$-fold expansion `qExpand ℚ q` of the series `lambdaModC ℚ`. The assertion is that the coefficientwise reduction of $\Psi$ modulo $q$, i.e. the image of $\Psi$ under the ring homomorphism `reduceModBivar q` obtained by applying `Int.castRingHom (ZMod q)` to all coefficients of all coefficients, equals the product $(Y^{q} - X)(Y - X^{q})$ in $(\mathbb{Z}/q\mathbb{Z})[Y][X]$ — equivalently $(X - Y^{q})(X^{q} - Y)$ — where $Y$ denotes the inner variable, written as the constant polynomial `Polynomial.C Polynomial.X`, and $X$ the outer one.
--
--   This is Kronecker's congruence for the modular equation attached to the level-two function $\lambda$: modulo $q$ the modular polynomial degenerates into the product of the two Frobenius factors. It is used in the proof that $\Psi$ is reciprocal and in the existence statement [`ModularCurve.exists_lambdaKroneckerCongruence`](thm.html#ModularCurve.exists_lambdaKroneckerCongruence), which supplies the congruence in the form needed later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_kroneckerCongruence_lambda.lean

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

theorem ModularCurve.kroneckerCongruence_lambda (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (data : LambdaModularPolynomialData q) :
    reduceModBivar q data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by sorry
