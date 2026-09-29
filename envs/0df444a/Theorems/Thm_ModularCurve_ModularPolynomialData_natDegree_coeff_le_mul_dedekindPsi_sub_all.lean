-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub_all
-- name    : ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub_all
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/16939f52-9287-53c3-987d-ccf8aaa5dd83
-- title:
--   Degree bound for the coefficients of Φ_N
-- statement:
--   Let $N$ be a natural number, nonzero, and let $\psi(N)$ denote `dedekindPsi N`, defined as $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ (equivalently $N\prod_{p \mid N}(1+1/p)$). Let `data` be a modular polynomial datum of level $N$, that is: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ (an element of `Polynomial (Polynomial ℤ)`) which is monic as a polynomial in $Y$, whose degree in $Y$ equals $\psi(N)$, and which satisfies $\Phi = 0$ when evaluated, via `Polynomial.eval₂`, with the coefficient ring $\mathbb{Z}[X]$ mapped into the field of Laurent series over $\mathbb{Q}$ by the ring homomorphism `evalAtJ` sending $X$ to the element `jq`, and with the variable $Y$ set equal to the element `jqN N`. Then for every natural number $i$, the coefficient of $Y^i$ in $\Phi$, an element of $\mathbb{Z}[X]$, has degree at most $N\,(\psi(N) - i)$, the subtraction being truncated subtraction of natural numbers (so for $i \ge \psi(N)$ the assertion is that this coefficient is constant).
--
--   This is the weighted-degree bound on the classical modular polynomial $\Phi_N(X,Y)$: $\Phi_N$ has weighted degree $N\psi(N)$ for the weights $(1,N)$ on $(X,Y)$, the integrality statement at the cusp which underlies the chart at infinity of an integral model of $X_0(N)$. It holds at every level, with no symmetry hypothesis, in contrast with the prime-level form [`ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub`](thm.html#ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub), which assumes `EvalSymm`; it is used in the construction recorded by [`ModularCurve.ModularPolynomialData.exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one`](thm.html#ModularCurve.ModularPolynomialData.exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub_all.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve Polynomial
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub_all (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (i : ℕ) :
    (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i) := by sorry
