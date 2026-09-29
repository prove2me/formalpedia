-- Prove2me | Theorems.Thm_ModularCurve_coeff_coeff_swapBivar
-- name    : ModularCurve.coeff_coeff_swapBivar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/c93cce1c-4739-58d1-b813-9a766dc3fa7f
-- title:
--   Coefficient transposition under the bivariate swap
-- statement:
--   Let $\Phi$ be an element of $\mathbb{Z}[X][Y]$, i.e. a polynomial in one variable over $\mathbb{Z}[X]$, and let $i,j$ be natural numbers. Here `swapBivar` is the ring homomorphism $\mathbb{Z}[X][Y]\to\mathbb{Z}[X][Y]$ obtained by evaluating the outer variable $Y$ at the constant $C\,X$ while mapping the coefficients in $\mathbb{Z}[X]$ through `swapInner`, the homomorphism $\mathbb{Z}[X]\to\mathbb{Z}[X][Y]$ that sends the variable of $\mathbb{Z}[X]$ to the outer variable $Y$ and a constant $d\in\mathbb{Z}$ to $C(C\,d)$; thus `swapBivar` interchanges the two variables. The assertion is the corresponding transposition of coefficient matrices: the coefficient of $X^i$ in the $Y^j$-coefficient of `swapBivar Φ` equals the coefficient of $X^j$ in the $Y^i$-coefficient of $\Phi$, i.e. writing $\Phi=\sum_{a,b} c_{a,b}\,X^{b}Y^{a}$ with $c_{a,b}\in\mathbb{Z}$, the coefficient matrix of `swapBivar Φ` has $(j,i)$-entry $c_{i,j}$. The identity holds for all $\Phi$, $i$ and $j$, with no hypotheses.
--
--   This is the coefficientwise description of the transpose operation on bivariate integer polynomials: passing from the substitution $X\leftrightarrow Y$ to the transposition of the coefficient matrix. It is used where symmetry of a modular polynomial under the swap must be converted into symmetry of its coefficients, in particular in the bidegree and coefficient-degree bounds for the modular polynomials and in the chart computations for the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_coeff_swapBivar.lean

import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Polynomial

theorem ModularCurve.coeff_coeff_swapBivar (Φ : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    ((swapBivar Φ).coeff j).coeff i = (Φ.coeff i).coeff j := by sorry
