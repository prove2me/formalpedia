-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul
-- name    : ModularCurve.ModularPolynomialData.dvd_resultant_of_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/318e7a9b-d11b-5159-9a5c-48f0dba7f4e4
-- title:
--   Divisibility of the composed modular polynomial by the resultant
-- statement:
--   Let $\ell$ and $M$ be nonzero natural numbers, and suppose given modular polynomial data $d_\ell$ at level $\ell$, $d_M$ at level $M$ and $d_N$ at level $\ell M$; such data at level $N$ consists of a polynomial $\Phi \in \mathbb{Z}[X][Y]$ that is monic in $Y$, of degree in $Y$ equal to $\sum_{d \mid N,\ d \text{ squarefree}} N/d$, and satisfies $\Phi(j(q), j(q^N)) = 0$ in the Laurent series field $\mathbb{Q}((q))$, the substitution being the evaluation $X \mapsto j(q)$ on coefficients together with $Y \mapsto j(q^N)$. Form, in the polynomial ring over $B = \mathbb{Z}[X][Y]$ in a further variable $Z$, the two polynomials: $f$, obtained from $d_\ell.\Phi$ by regarding its $Y$-variable as $Z$ and its coefficients in $\mathbb{Z}[X]$ as constants of $B$; and $g$, obtained from $d_M.\Phi$ by substituting $Z$ for the variable $X$ of its coefficients and $Y$ for its $Y$-variable, i.e. $f = \Phi_\ell(X,Z)$ and $g = \Phi_M(Z,Y)$. The conclusion is that $d_N.\Phi$ divides the resultant of $f$ and $g$ in $Z$, as elements of $\mathbb{Z}[X][Y]$. No coprimality of $\ell$ and $M$ is assumed.
--
--   This is the composition law for modular correspondences: the modular polynomial of level $\ell M$ divides $\operatorname{Res}_Z(\Phi_\ell(X,Z), \Phi_M(Z,Y))$, the algebraic shadow of the relation $T_\ell T_M$ between Hecke correspondences on modular curves. It is used in the analysis of the roots of the modular polynomial at a transcendental $j$-invariant, namely by [`WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`](thm.html#WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_dvd_resultant_of_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.ModularPolynomialData.dvd_resultant_of_mul
    (ℓ M : ℕ) [NeZero ℓ] [NeZero M]
    (dℓ : ModularPolynomialData ℓ) (dM : ModularPolynomialData M)
    (dN : ModularPolynomialData (ℓ * M)) :
    dN.Φ ∣ (dℓ.Φ.map (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ))).resultant
      (dM.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom (Polynomial (Polynomial ℤ))))
        (Polynomial.C Polynomial.X)) := by sorry
