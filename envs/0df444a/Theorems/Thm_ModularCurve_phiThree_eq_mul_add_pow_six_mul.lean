-- Prove2me | Theorems.Thm_ModularCurve_phiThree_eq_mul_add_pow_six_mul
-- name    : ModularCurve.phiThree_eq_mul_add_pow_six_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/3f251cba-226a-5925-81fb-775774af86f7
-- title:
--   Factorisation of Φ₃ modulo 3⁶
-- statement:
--   Work in $\mathbb{Z}[X][Y]$, the polynomial ring in one variable $Y$ over $\mathbb{Z}[X]$ (in the Lean text $Y$ is the outer variable `X` and $x =$ `C X` is the image of the inner variable). The element `phiThree` is by definition $Y^4 + c_3 Y^3 + c_2 Y^2 + c_1 Y + c_0$ with coefficients in $\mathbb{Z}[X]$ given by $c_3 = -X^3 + 2232X^2 - 1069956X + 36864000$, $c_2 = 2232X^3 + 2587918086X^2 + 8900222976000X + 452984832000000$, $c_1 = -1069956X^3 + 8900222976000X^2 - 770845966336000000X + 1855425871872000000000$ and $c_0 = X^4 + 36864000X^3 + 452984832000000X^2 + 1855425871872000000000X$. The theorem asserts the identity, with no hypotheses, $$\mathrm{phiThree} = (x^3 + 684x^2 + 513x + 27 - Y)\,(x - Y^3 + 45Y^2 + 216Y + 702) + 3^6\, r,$$ where $$r = (-26 + 2545165805037036543\,x + 621378369711\,x^2 + 50566\,x^3) + (2545165805037037030 - 1057401874260783\,x + 12208810464\,x^2 - 1468\,x^3)Y + (621378370369 + 12208810635\,x + 3549914\,x^2 + 3\,x^3)Y^2 + (50568 - 1467\,x + 4\,x^2)Y^3 .$$
--
--   The polynomial `phiThree` is the classical modular polynomial $\Phi_3$, and the identity is an explicit certificate that its Kronecker factorisation $(X^3-Y)(X-Y^3)$ modulo $3$ lifts to a factorisation modulo $3^6$, with the two factors displayed and the error term divisible exactly by $3^6$ (its constant term is $-26$). It is used in the analysis of the local structure of the modular curve at the point in question, namely by [`ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_three`](thm.html#ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_three) and by [`ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five`](thm.html#ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_phiThree_eq_mul_add_pow_six_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_ClassicalModularPolynomials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial ModularCurve

theorem ModularCurve.phiThree_eq_mul_add_pow_six_mul :
    phiThree
      = ((C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 3 + 684 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 + 513 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 27 - (X : Polynomial (Polynomial ℤ))) * ((C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) - (X : Polynomial (Polynomial ℤ)) ^ 3 + 45 * (X : Polynomial (Polynomial ℤ)) ^ 2 + 216 * (X : Polynomial (Polynomial ℤ)) + 702)
        + 3 ^ 6 * ((-26 + 2545165805037036543 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 621378369711 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 + 50566 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 3)
                   + (2545165805037037030 - 1057401874260783 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 12208810464 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 - 1468 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 3) * (X : Polynomial (Polynomial ℤ))
                   + (621378370369 + 12208810635 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 3549914 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 + 3 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 3) * (X : Polynomial (Polynomial ℤ)) ^ 2
                   + (50568 - 1467 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 4 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2) * (X : Polynomial (Polynomial ℤ)) ^ 3) := by sorry
