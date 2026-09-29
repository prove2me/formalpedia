-- Prove2me | Theorems.Thm_ModularCurve_pointEval_kroneckerRemainder
-- name    : ModularCurve.pointEval_kroneckerRemainder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/35e02aaf-20fa-5352-8576-a88da8bbd683
-- title:
--   Point evaluation of a transported integral polynomial
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} \colon A \to k$, a polynomial $R$ in $\mathbb{Z}[\,\cdot\,][\,\cdot\,]$ (a polynomial in an outer variable whose coefficients are polynomials in an inner variable over $\mathbb{Z}$), and elements $a, b \in k$. Transport $R$ into $A[X_0, X_1]$ by sending the inner variable to $X_0$, the outer variable to $X_1$, and the integer coefficients into $A$ by the canonical ring homomorphism $\mathbb{Z} \to A$. The assertion is that applying `NodeLocalized.pointEval` for $A$, $\mathrm{red}$, $a$, $b$ — that is, the evaluation homomorphism $A[X_0,X_1] \to k$ acting on coefficients by $\mathrm{red}$ and sending $X_0 \mapsto a$, $X_1 \mapsto b$ — to this transported element yields the same value as the classical recipe on the right-hand side: reduce the integer coefficients of $R$ coefficientwise by $\mathbb{Z} \to k$, substitute the constant $b$ for the outer variable to obtain an element of $k[X]$, and evaluate that at $a$. Both sides are thus $\bar R(a,b)$. The proof uses neither the primality of $q$, nor the characteristic hypothesis on $k$, nor the fact that $A$ is a valuation subring; these only fix the ambient setting.
--
--   This is the dictionary lemma identifying the point evaluation attached to a localized nodal ring with the naive reduce-and-substitute value $\bar R(a,b)$ of an integral bivariate polynomial; it is used when Kronecker-type remainders for the modular polynomial are evaluated at points of the special fibre. It is cited in the analysis of local rings of the modular curve at points of the fibre above $q$, in particular in the constructions of crossing presentations and the determination of primes lying over the descended nodal ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pointEval_kroneckerRemainder.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.pointEval_kroneckerRemainder
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (R : Polynomial (Polynomial ℤ)) (a b : k) :
    NodeLocalized.pointEval A.toSubring red a b
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
        (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)
      = ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C b)).eval a := by sorry
