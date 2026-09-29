-- Prove2me | Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
-- name    : ModularCurve.eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/cb96422f-3c9f-533c-8c6e-95d8f91fd1ad
-- title:
--   Non-vanishing of the reduced Kronecker remainder at supersingular j
-- statement:
--   Let $q$ be a prime with $5 \le q$, and let `data` be a `ModularPolynomialData q`, that is: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ (coefficients in $\mathbb{Z}[X]$, outer variable $Y$) which is monic, whose degree in the outer variable $Y$ equals $\psi(q)=\sum_{d \mid q,\ d \text{ squarefree}} q/d$, and which vanishes when $X$ is specialised to the $q$-expansion of $j$ (through `evalAtJ`) and $Y$ to `jqN q`. Let $R \in \mathbb{Z}[X][Y]$ be such that the Kronecker decomposition $\Phi = (X^q - Y)(X - Y^q) + q\,R$ holds. Let $k$ be an algebraically closed field of characteristic $q$, and let $a \in k$ satisfy: $a$ lies in `ssJSet q k`, i.e. every Weierstrass curve over $k$ which is elliptic and has $j$-invariant $a$ has no nonzero affine point killed by $q$; and $a \ne 0$, $a \ne 1728$. Then the reduction of $R$ modulo $q$ (coefficientwise image under $\mathbb{Z} \to k$), evaluated at $Y = a^q$ and then at $X = a$, is nonzero: $\bar R(a, a^q) \ne 0$.
--
--   This is the width-one unit criterion arising from Kronecker's congruence $\Phi_q \equiv (X^q-Y)(X-Y^q) \bmod q$: at a supersingular $j$-invariant other than $0$ and $1728$ the remainder term does not vanish, so the corresponding singular point of the reduction of $X_0(q)$ in characteristic $q$ is an ordinary double point with the expected local invariant. It is used throughout the subsequent local analysis of the nodes of $X_0(q)$ in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Polynomial in

theorem ModularCurve.eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (data : ModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet q k) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ((R.map (mapRingHom (Int.castRingHom k))).eval (C (a ^ q))).eval a ≠ 0 := by sorry
