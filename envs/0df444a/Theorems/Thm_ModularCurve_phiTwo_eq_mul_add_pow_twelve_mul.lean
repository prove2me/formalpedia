-- Prove2me | Theorems.Thm_ModularCurve_phiTwo_eq_mul_add_pow_twelve_mul
-- name    : ModularCurve.phiTwo_eq_mul_add_pow_twelve_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/278cb6e7-336b-5a7f-9c8b-d7230b4000e3
-- title:
--   Explicit 2-adic factorisation identity for Φ₂
-- statement:
--   The assertion is an identity in $\mathbb{Z}[x][y]$, where `phiTwo` denotes the polynomial $y^3 + (-x^2+1488x-162000)\,y^2 + (1488x^2+40773375x+8748000000)\,y + (x^3-162000x^2+8748000000x-157464000000000)$, the outer variable being $y$ and the coefficient variable $x$ (entering through `C`). The theorem states that this polynomial equals
--   $$\bigl(x^2+2608x+768-y\bigr)\bigl(x-y^2+1488y+3328\bigr)+2^{12}\,r(x,y),$$
--   with
--   $$r(x,y)=\bigl(-38443359999+2133623\,x-41\,x^2\bigr)+\bigl(2135464+9007\,x\bigr)y+\bigl(-39+x\bigr)y^2 .$$
--   There are no variables or hypotheses: the statement is a closed equality between two explicit elements of $\mathbb{Z}[x][y]$. Modulo $2$ the two displayed factors become $x^2-y$ and $x-y^2$, and the remainder term is weighted exactly by $2^{12}$; the constant term $r(0,0)=-38443359999$ is odd, so no higher power of $2$ can be extracted from the remainder at the origin.
--
--   The polynomial `phiTwo` is the classical modular polynomial $\Phi_2$ relating the $j$-invariants of $2$-isogenous elliptic curves, and the identity records how its Kronecker factorisation $\Phi_2 \equiv (x^2-y)(x-y^2) \bmod 2$ lifts over $\mathbb{Z}$ with an error divisible by exactly $2^{12}$ at the origin. It is used in the analysis of the singularity of $X_0(2)$ at the supersingular point, namely by [`ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two`](thm.html#ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_q_eq_two) and [`ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five`](thm.html#ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_phiTwo_eq_mul_add_pow_twelve_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_ClassicalModularPolynomials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial ModularCurve

theorem ModularCurve.phiTwo_eq_mul_add_pow_twelve_mul :
    phiTwo
      = ((C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 + 2608 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 768 - (X : Polynomial (Polynomial ℤ))) * ((C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) - (X : Polynomial (Polynomial ℤ)) ^ 2 + 1488 * (X : Polynomial (Polynomial ℤ)) + 3328)
        + 2 ^ 12 * ((-38443359999 + 2133623 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) - 41 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2)
                    + (2135464 + 9007 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ))) * (X : Polynomial (Polynomial ℤ)) + (-39 + (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ))) * (X : Polynomial (Polynomial ℤ)) ^ 2) := by sorry
