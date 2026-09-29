-- Prove2me | Theorems.Thm_ModularCurve_lambdaKroneckerRemainder_frobeniusGraph_ode
-- name    : ModularCurve.lambdaKroneckerRemainder_frobeniusGraph_ode
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/3ed1ea85-2d7e-50da-9cb7-6493e13a2644
-- title:
--   Wronskian closed form for the λ-line Kronecker remainder
-- statement:
--   Let $q$ be a prime with $q\ge 5$, and let `data` be a `LambdaModularPolynomialData q`, that is, a polynomial $\Psi \in (\mathbb{Z}[X])[Y]$ which is monic of degree $q+1$ in $Y$ and which vanishes when its coefficients are evaluated at the integral $\lambda$-series `lambdaInt` (pushed into Laurent series over $\mathbb{Q}$) and $Y$ is set equal to `lambdaNModC ℚ q`, the level-$q$ expansion $\mathrm{qExpand}\,\mathbb{Q}\,q$ of the series `lambdaModC ℚ`; so $\Psi$ is a modular equation of level $q$ for $\lambda$. Let $R \in (\mathbb{Z}[X])[Y]$ satisfy the Kronecker-type decomposition $\Psi = (C(X)^q - Y)\,(C(X) - Y^q) + q\,R$, where $C(X)$ denotes the constant-in-$Y$ polynomial given by the inner variable. Let $k$ be a field of characteristic $q$. Put $G \in k[X]$ for the image in $k[X]$ of $R$ evaluated at $Y = X^q$, i.e. the reduction mod $q$ of $R(X,X^q)$; put $F := X^{q^2} - X$; and put $H := \bar H_q(16X)$, where $\bar H_q$ is the reduction mod $q$ of the Deuring polynomial $\sum_{i=0}^{(q-1)/2} \binom{(q-1)/2}{i}^2 X^i$. The assertion is the identity in $k[X]$ $$\bigl(G'F - GF'\bigr)H^2 = \bigl(X^{q-1}H^2 - (X(1-16X))^{q-1}\bigr)F^2 .$$
--
--   This is the level-two ($\lambda$-line) form of Kronecker's congruence carried to second order: rewritten as $\frac{d}{dX}(G/F) = X^{q-1} - (X(1-16X))^{q-1}/H^2$, it expresses the logarithmic derivative of the reduced Kronecker remainder in terms of the Deuring polynomial, whose roots correspond to supersingular values of $\lambda$. It is used by [`ModularCurve.eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial`](thm.html#ModularCurve.eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial) to rule out vanishing of the reduced remainder at such values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_lambdaKroneckerRemainder_frobeniusGraph_ode.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_Polynomial_DeuringPolynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.lambdaKroneckerRemainder_frobeniusGraph_ode
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (data : LambdaModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (k : Type*) [Field k] [CharP k q] :
    let G : Polynomial k := (R.eval (Polynomial.X ^ q)).map (Int.castRingHom k)
    let F : Polynomial k := Polynomial.X ^ (q ^ 2) - Polynomial.X
    let H : Polynomial k := ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).comp (16 * Polynomial.X)
    (Polynomial.derivative G * F - G * Polynomial.derivative F) * H ^ 2 =
      (Polynomial.X ^ (q - 1) * H ^ 2 - (Polynomial.X * (1 - 16 * Polynomial.X)) ^ (q - 1)) * F ^ 2 := by sorry
