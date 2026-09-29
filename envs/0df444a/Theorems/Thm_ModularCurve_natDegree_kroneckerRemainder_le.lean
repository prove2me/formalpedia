-- Prove2me | Theorems.Thm_ModularCurve_natDegree_kroneckerRemainder_le
-- name    : ModularCurve.natDegree_kroneckerRemainder_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/215e3e6a-4058-570d-8d92-aa634e0ba79f
-- title:
--   Degree bounds for the Kronecker congruence remainder
-- statement:
--   Let $q$ be a prime and let `data` be a `ModularPolynomialData q`: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ (the inner variable written $X$, the outer one $Y$) which is monic in $Y$, whose $Y$-degree equals `dedekindPsi q`, the sum of $q/d$ over the squarefree divisors $d$ of $q$ (this equals $q+1$ for $q$ prime), and which satisfies $\Phi = 0$ after the substitution sending $X$ to the Laurent series `jq` — that is, via the ring homomorphism `evalAtJ` $\colon \mathbb{Z}[X] \to \mathrm{LaurentSeries}\,\mathbb{Q}$ — and $Y$ to `jqN q`. Let $R \in \mathbb{Z}[X][Y]$ be a further polynomial subject to the hypothesis that $$\Phi = (X^{q} - Y)(X - Y^{q}) + q\,R .$$ The conclusion is threefold: the $Y$-degree of $R$ is at most $q$; for every $k$ the coefficient of $Y^{k}$ in $R$, an element of $\mathbb{Z}[X]$, has $X$-degree at most $q$; and the coefficient of $X^{q}Y^{q}$ in $R$ vanishes. No total-degree bound on $R$ is asserted.
--
--   This records the shape of the remainder in the Kronecker congruence $\Phi_q(X,Y) \equiv (X^{q}-Y)(X-Y^{q}) \pmod q$ for the modular polynomial of prime level $q$: the quotient $R$ is bidegree-bounded by $q$ and misses the monomial $X^{q}Y^{q}$. The bounds are used in the analysis of the plane model of $X_0(q)$ near its singular and cuspidal points, in [`ModularCurve.PlaceSpecialization.eq_of_isInftySide_of_hasValue_jFun`](thm.html#ModularCurve.PlaceSpecialization.eq_of_isInftySide_of_hasValue_jFun) and [`ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal`](thm.html#ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natDegree_kroneckerRemainder_le.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve

theorem ModularCurve.natDegree_kroneckerRemainder_le
    (q : ℕ) [Fact q.Prime] (data : ModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
            + Polynomial.C (Polynomial.C (q : ℤ)) * R) :
    R.natDegree ≤ q ∧ (∀ k, (R.coeff k).natDegree ≤ q) ∧ (R.coeff q).coeff q = 0 := by sorry
