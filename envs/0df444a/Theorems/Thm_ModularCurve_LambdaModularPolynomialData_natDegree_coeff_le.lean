-- Prove2me | Theorems.Thm_ModularCurve_LambdaModularPolynomialData_natDegree_coeff_le
-- name    : ModularCurve.LambdaModularPolynomialData.natDegree_coeff_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/df45a28f-b2c1-59a2-b3de-2e97369df01e
-- title:
--   Every Y-coefficient of Ψ has X-degree at most q+1
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and let `data` be a `LambdaModularPolynomialData q`, that is: a polynomial $\Psi \in (\mathbb{Z}[X])[Y]$ in one variable over $\mathbb{Z}[X]$, which is monic, has `natDegree` equal to $q+1$, and satisfies the vanishing condition `eval_eq_zero`: substituting for $Y$ the Laurent series `lambdaNModC ℚ q`, namely the $q$-fold $q$-expansion `qExpand ℚ q` of `lambdaModC ℚ`, and interpreting the coefficients in $\mathbb{Z}[X]$ through the ring homomorphism `evalAtLambdaInt`, which sends $X$ to `lambdaInt` inside `LaurentSeries ℤ`, followed by the coefficientwise map `laurentMap` of $\mathbb{Z} \to \mathbb{Q}$ on Laurent series, yields $0$. Then for every natural number $k$ the coefficient of $Y^k$ in $\Psi$, an element of $\mathbb{Z}[X]$, has `natDegree` at most $q+1$. The bound is asserted for all $k$, including those exceeding $q+1$, where the coefficient vanishes or is constant. The proof cites the reformulated vanishing statement [`ModularCurve.LambdaModularPolynomialData.eval2_swap_eq_zero`](thm.html#ModularCurve.LambdaModularPolynomialData.eval2_swap_eq_zero) with the roles of the two series interchanged, the identification [`ModularCurve.minpoly_lambdaNModC_eq`](thm.html#ModularCurve.minpoly_lambdaNModC_eq) of $\Psi$ with a minimal polynomial, and the transcendence [`ModularCurve.transcendental_lambdaModC`](thm.html#ModularCurve.transcendental_lambdaModC) of `lambdaModC` over the base ring.
--
--   This is the $X$-degree half of the classical statement that the modular polynomial relating the level-two modular function $\lambda$ at $\tau$ and at $q\tau$ has bidegree $(q+1, q+1)$; together with the monic degree $q+1$ condition in $Y$ it makes $\Psi$ symmetric in shape. It is the degree input used by [`ModularCurve.LambdaModularPolynomialData.psi_reciprocal`](thm.html#ModularCurve.LambdaModularPolynomialData.psi_reciprocal), and thence by [`ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_inv`](thm.html#ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_inv), where the coefficientwise reciprocity relations are converted into the polynomial identity expressing the involution $\lambda \mapsto 1/\lambda$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LambdaModularPolynomialData_natDegree_coeff_le.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaModularPolynomialData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.LambdaModularPolynomialData.natDegree_coeff_le
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) (k : ℕ) :
    (data.Ψ.coeff k).natDegree ≤ q + 1 := by sorry
