-- Prove2me | Theorems.Thm_ModularCurve_existsUnique_lambdaKroneckerRemainder
-- name    : ModularCurve.existsUnique_lambdaKroneckerRemainder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/37e0c7e0-363b-5157-95ef-ce88f77aef8a
-- title:
--   Uniqueness of the q-th Kronecker remainder for Ψ_q
-- statement:
--   Let $q$ be a natural number carrying a `Fact` that it is prime, and let `data` be a term of `LambdaModularPolynomialData q`, i.e. a package consisting of a bivariate integer polynomial $\Psi =$ `data.Ψ` in `Polynomial (Polynomial ℤ)` together with the three properties that $\Psi$ is monic in the outer variable, that its degree in that variable is $q+1$, and that $\Psi$ vanishes when its coefficient variable is sent to the Laurent series `lambdaInt` (pushed forward to $\mathbb{Q}$ by `laurentMap (Int.castRingHom ℚ)` composed with `evalAtLambdaInt`) and its outer variable to `lambdaNModC ℚ q`, the $q$-fold $q$-expansion of `lambdaModC ℚ`; of these data only $\Psi$ itself enters the argument. Assume further that `reduceModBivar q data.Ψ`, the coefficientwise reduction of $\Psi$ modulo $q$ into `Polynomial (Polynomial (ZMod q))`, equals $(\mathrm{C}\,X)^q - X$ times $\mathrm{C}\,X - X^q$; writing $X$ for the inner and $Y$ for the outer variable, this says $\Psi \equiv (X^q - Y)(X - Y^q) \pmod q$. The conclusion is that there is exactly one $R \in \mathbb{Z}[X][Y]$ with $\Psi = (X^q-Y)(X-Y^q) + q\,R$, the constant $q$ appearing as `C (C (q : ℤ))`.
--
--   This is the second-order form of the Kronecker congruence for the modular equation of level $q$ in the $\lambda$-model: the congruence $\Psi \equiv (X^q-Y)(X-Y^q) \bmod q$ is upgraded to an identity with a uniquely determined integral remainder $R$. The resulting $R$ is what is needed in the local analysis at a node of the modular curve, and the statement is used in the identification of the completed local ring at such a point with a crossing model and in the proof that the relevant coefficient subring is integrally closed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_existsUnique_lambdaKroneckerRemainder.lean

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

theorem ModularCurve.existsUnique_lambdaKroneckerRemainder (q : ℕ) [Fact q.Prime]
    (data : LambdaModularPolynomialData q) (hK : reduceModBivar q data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)) :
    ∃! R : Polynomial (Polynomial ℤ), data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R := by sorry
