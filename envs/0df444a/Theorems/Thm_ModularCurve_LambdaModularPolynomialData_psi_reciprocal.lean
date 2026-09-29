-- Prove2me | Theorems.Thm_ModularCurve_LambdaModularPolynomialData_psi_reciprocal
-- name    : ModularCurve.LambdaModularPolynomialData.psi_reciprocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/335cff3b-ea05-5ebc-acff-006f1bf2e635
-- title:
--   Reciprocal symmetry of the modular polynomial Ψ_q
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and let `data` be a `LambdaModularPolynomialData q`, that is: a polynomial $\Psi \in \mathbb{Z}[X][Y]$ (denoted `data.Ψ`) which is monic in $Y$ of degree $q+1$ and which vanishes when one substitutes $Y \mapsto$ `lambdaNModC ℚ q` (the level-$q$ expansion `qExpand ℚ q` of the Laurent series `lambdaModC ℚ`) and applies to the coefficients in $\mathbb{Z}[X]$ the ring homomorphism `evalAtLambdaInt`, evaluation at the Laurent series `lambdaInt`, followed by the coefficientwise map of Laurent series induced by $\mathbb{Z} \to \mathbb{Q}$. Write $c_{i,k} =$ `(data.Ψ.coeff k).coeff i` for the coefficient of $X^i Y^k$ in $\Psi$. Then for all natural numbers $i, k$ with $i + k \le q+1$ one has
--   $$c_{\,q+1-i,\;q+1-k} \;=\; 256^{\,q+1-i-k}\, c_{i,k},$$
--   all subtractions being in $\mathbb{N}$; the hypothesis $i + k \le q+1$ guarantees that none of them is truncated. Equivalently, $(256XY)^{q+1}\,\Psi\bigl(1/(256X),\,1/(256Y)\bigr) = \Psi(X,Y)$, in coefficient form.
--
--   This is the functional equation of the level-two modular polynomial of level $q$ under the anharmonic involution $\lambda \mapsto 1/\lambda$ of $X(2)$, in the normalisation in which it reads $\mu \mapsto 1/(256\mu)$, and it expresses that this involution commutes with the level-$q$ correspondence. It is used in the local study of the nodes of the $\lambda$-modular curve, namely in [`ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_inv`](thm.html#ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_inv), to transport statements at one branch to the branch obtained by inversion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LambdaModularPolynomialData_psi_reciprocal.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaModularPolynomialData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.LambdaModularPolynomialData.psi_reciprocal
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q)
    (i k : ℕ) (hik : i + k ≤ q + 1) :
    (data.Ψ.coeff (q + 1 - k)).coeff (q + 1 - i) = 256 ^ (q + 1 - i - k) * (data.Ψ.coeff k).coeff i := by sorry
