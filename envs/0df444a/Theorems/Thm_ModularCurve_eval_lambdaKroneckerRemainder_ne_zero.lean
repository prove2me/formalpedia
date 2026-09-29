-- Prove2me | Theorems.Thm_ModularCurve_eval_lambdaKroneckerRemainder_ne_zero
-- name    : ModularCurve.eval_lambdaKroneckerRemainder_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/8d6cd025-db6b-5ede-b9db-c4b68482e5f8
-- title:
--   Kronecker remainder non-vanishing at supersingular λ-values
-- statement:
--   Let $q$ be a prime with $q \ge 5$ and let `data` be an element of `LambdaModularPolynomialData q`, that is, a polynomial $\Psi \in (\mathbb{Z}[X])[X]$ which is monic, has degree $q+1$, and satisfies $\Psi = 0$ after the coefficient ring $\mathbb{Z}[X]$ is sent into $\mathbb{Z}((T))$ by evaluation at the Laurent series `lambdaInt` and thence to $\mathbb{Q}((T))$, the remaining variable being specialised to `lambdaNModC ℚ q`, the $q$-fold $q$-expansion of `lambdaModC ℚ`. Let $R \in (\mathbb{Z}[X])[X]$ be such that $\Psi = (C\,X^{q} - X)\,(C\,X - X^{q}) + q\,R$, where $C$ denotes the inclusion of the coefficient ring; that is, in bivariate notation $\Psi(u,v) = (u^{q}-v)(u-v^{q}) + qR(u,v)$. Let $k$ be an algebraically closed field of characteristic $q$ and let $l \in k$ satisfy $l \ne 0$ and $16l \ne 1$. Assume there exists $a \in k$ with $a\,\bigl((16l)^{2}(16l-1)^{2}\bigr) = 256\,\bigl((16l)^{2} - 16l + 1\bigr)^{3}$ such that $a$ lies in `ssJSet q k`, the set of $j \in k$ with the property that every elliptic Weierstrass curve $W$ over $k$ of $j$-invariant $j$ has no non-zero affine point killed by $q$. Then the image $\bar R$ of $R$ under coefficientwise reduction to $(k[X])[X]$, evaluated at the constant polynomial $l^{q}$ in the outer variable and at $l$ in the inner variable, is non-zero.
--
--   This is the statement that the second-order term of the Kronecker level-two modular equation is a unit at every supersingular $\lambda$-node, the supersingularity hypothesis being phrased through the $j$-invariant $256((16l)^2-16l+1)^3 / ((16l)^2(16l-1)^2)$ of the Legendre curve with parameter $16l$. It is used in the local study of the plane model of the $\lambda$-curve at such a point, namely in the identification of the completed local ring with a crossing model and in the integral closedness of the coefficient subring attached to the point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eval_lambdaKroneckerRemainder_ne_zero.lean

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

theorem ModularCurve.eval_lambdaKroneckerRemainder_ne_zero
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (data : LambdaModularPolynomialData q) (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R)
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (l : k) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hss : ∃ a ∈ ssJSet q k, a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
    ((R.map (mapRingHom (Int.castRingHom k))).eval (C (l ^ q))).eval l ≠ 0 := by sorry
