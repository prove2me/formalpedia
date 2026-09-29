-- Prove2me | Theorems.Thm_ModularCurve_kroneckerRemainder_frobeniusGraph_ode
-- name    : ModularCurve.kroneckerRemainder_frobeniusGraph_ode
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/3d631cea-577b-5413-881a-713b2ed65879
-- title:
--   Closed form for the Kronecker remainder Wronskian
-- statement:
--   Let $q\ge 5$ be a prime and let `data` be a `ModularPolynomialData q`, that is, a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q)=\sum_{d\mid q,\ d\ \text{squarefree}} q/d$ in its outer variable which is annihilated by substituting the $j$-Laurent series for the inner variable and $j(q\tau)$ for the outer one. Let $R\in\mathbb{Z}[X][Y]$ satisfy the Kronecker decomposition $\Phi=(C(X)^q-X)\,(C(X)-X^q)+q\,R$, and let natural numbers $m,e_4,e_6$ satisfy $12m+4e_4+6e_6=q-1$, $e_4\le 2$, $e_6\le 1$. Let $k$ be an algebraically closed field of characteristic $q$, and let $S_0\subseteq k$ be a finite set whose members are exactly the $j\in k$ such that every elliptic Weierstrass curve over $k$ with $j$-invariant $j$ has no nonzero point killed by $q$ (the supersingular $j$-invariants). Put $G:=R(X^q)\bmod q\in k[X]$ (the outer variable specialised to $X^q$, coefficients reduced to $k$), $F:=X^{q^2}-X$ and $s:=\prod_{a\in S_0\setminus\{0,1728\}}(X-a)$. The conclusion is the identity in $k[X]$
--   $$(G'F-GF')\,s^2=\bigl(X^{q-1}s^2-X^{8m+2e_4+4e_6}(X-1728)^{6m+2e_4+2e_6}\bigr)F^2 ,$$
--   i.e. $\,(G/F)'=X^{q-1}-X^{8m+2e_4+4e_6}(X-1728)^{6m+2e_4+2e_6}/s^2$.
--
--   This is the closed-form differential identity satisfied by the reduction mod $q$ of the remainder term in the Kronecker congruence for the modular polynomial of level $q$, with the supersingular polynomial appearing as the denominator; it is obtained by transporting an identity between $\theta$-operator expressions in $k((\mathfrak q))$ along the transcendental element $\bar\jmath$. It is used to show that the Kronecker remainder does not vanish at a supersingular $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_kroneckerRemainder_frobeniusGraph_ode.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve

theorem ModularCurve.kroneckerRemainder_frobeniusGraph_ode
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (data : ModularPolynomialData q)
    (R : Polynomial (Polynomial ℤ))
    (hR : data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
            + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    let G : Polynomial k := (R.eval (Polynomial.X ^ q)).map (Int.castRingHom k)
    let F : Polynomial k := Polynomial.X ^ (q ^ 2) - Polynomial.X
    let s : Polynomial k := ∏ a ∈ S₀ \ {0, 1728}, (Polynomial.X - Polynomial.C a)
    (Polynomial.derivative G * F - G * Polynomial.derivative F) * s ^ 2 =
      (Polynomial.X ^ (q - 1) * s ^ 2
        - Polynomial.X ^ (8 * m + 2 * e₄ + 4 * e₆) * (Polynomial.X - Polynomial.C 1728) ^ (6 * m + 2 * e₄ + 2 * e₆)) * F ^ 2 := by sorry
