-- Prove2me | Theorems.Thm_ModularCurve_eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial
-- name    : ModularCurve.eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/a1641c91-e0e6-5f20-bb65-65daf7563d8d
-- title:
--   Kronecker remainder is nonzero at supersingular λ-points
-- statement:
--   Let $q \ge 5$ be a prime. Let `data` be a `LambdaModularPolynomialData q`, that is, a polynomial $\Psi \in \mathbb{Z}[X][Y]$ (an element of `Polynomial (Polynomial ℤ)`) which is monic of degree $q+1$ in the outer variable and which vanishes when its outer variable is specialised to the Laurent series `lambdaNModC ℚ q` and its coefficients are pushed forward along `evalAtLambdaInt` (evaluation of an integer polynomial at the $\lambda$-series `lambdaInt`) followed by the coefficientwise map $\mathbb{Z} \to \mathbb{Q}$ of Laurent series. Let $R \in \mathbb{Z}[X][Y]$ satisfy the Kronecker-type decomposition $\Psi = (Y^{q} - X)(Y - X^{q}) + q\,R$, where $Y$ denotes the inner variable and $X$ the outer one. Let $k$ be a field of characteristic $q$ and let $l \in k$ be a root of the reduction modulo $q$ of the Deuring polynomial $\sum_{i=0}^{(q-1)/2} \binom{(q-1)/2}{i}^{2} X^{i}$ evaluated at $16l$. The conclusion is that the reduction $\bar R \in k[X][Y]$ of $R$, evaluated at the outer variable $X = l^{q}$ and then at the inner variable $Y = l$, is nonzero.
--
--   This is the statement that the second-order term of the Kronecker congruence for the level-$q$ modular polynomial of the $\lambda$-function is a unit at every supersingular point, the supersingular locus being cut out in the $\lambda$-coordinate by the Deuring (Hasse) polynomial evaluated at $16\lambda$; in geometric terms the corresponding crossings on the reduction modulo $q$ of the modular curve with $\Gamma(2)$-structure have width one. It feeds the companion statement [`ModularCurve.eval_lambdaKroneckerRemainder_ne_zero`](thm.html#ModularCurve.eval_lambdaKroneckerRemainder_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve
open Polynomial in

theorem ModularCurve.eval_lambdaKroneckerRemainder_ne_zero_of_deuringPolynomial
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (data : LambdaModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    {k : Type*} [Field k] [CharP k q]
    (l : k) (hl : ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).eval (16 * l) = 0) :
    ((R.map (mapRingHom (Int.castRingHom k))).eval (C (l ^ q))).eval l ≠ 0 := by sorry
