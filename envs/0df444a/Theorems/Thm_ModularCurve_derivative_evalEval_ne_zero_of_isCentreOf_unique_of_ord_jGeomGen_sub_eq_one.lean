-- Prove2me | Theorems.Thm_ModularCurve_derivative_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jGeomGen_sub_eq_one
-- name    : ModularCurve.derivative_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jGeomGen_sub_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/9152c444-cdfa-584a-b36d-e6e2b18c801c
-- title:
--   Unique centre with uniformiser gives partial_YΦ̄_N(c)≠ 0
-- statement:
--   Let $q$ be a prime and $k$ an algebraically closed field of characteristic $q$, and let $N\ge 1$ be an integer with $q\nmid N$. Let `data` be a `ModularPolynomialData N`, that is, a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\sum_{d\mid N,\ d\text{ squarefree}} N/d$ in $Y$ satisfying $\Phi(j_q,\,j_{q^N})=0$ after substituting the integral $j$-Laurent series for $X$ and the $N$-fold $q$-expansion of it for $Y$. Work inside the field $F=$ `modularFunctionFieldC k N`, the subfield of the Laurent series field $k((q))$ generated over $k$ by the two series `jqModC k` and `jqNModC k N`, whose images in $F$ are written $\tilde\jmath=$ `jGeomGen k N` and $\tilde\jmath_N=$ `jNGeomGen k N`. Let $v$ be a place of $F$ over $k$, i.e. a valuation subring of $F$ containing $k$, distinct from $F$, and a principal ideal ring, with $\operatorname{ord}_v$ the associated normalised integer valuation. Let $c=(c_1,c_2)\in k\times k$ be a centre of $v$, meaning $\operatorname{ord}_v(\tilde\jmath-c_1)>0$ and $\operatorname{ord}_v(\tilde\jmath_N-c_2)>0$, assume $v$ is the only place of $F$ over $k$ having $c$ as a centre, and assume $\operatorname{ord}_v(\tilde\jmath-c_1)=1$. Then the reduction $\bar\Phi$ of $\Phi$ with coefficients mapped into $k$ satisfies $(\partial\bar\Phi/\partial Y)(c_1,c_2)\neq 0$, the derivative being taken in the outer variable $Y$ and the result evaluated at $X=c_1$, $Y=c_2$.
--
--   This is the simple-point criterion for the affine plane model $\bar\Phi_N(X,Y)=0$ of the level-$N$ modular curve in characteristic $q\nmid N$: a point $c$ of the plane model carrying a single place at which $\tilde\jmath-c_1$ is a uniformiser is non-singular with non-vertical tangent. It is the converse of the implications going from $\partial_Y\bar\Phi_N(c)\neq 0$ to uniqueness of the place centred at $c$ and to $\tilde\jmath-c_1$ being a uniformiser, and it is used to produce chart data and model statements for prolongation tuples of place specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_derivative_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jGeomGen_sub_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve Polynomial

theorem ModularCurve.derivative_evalEval_ne_zero_of_isCentreOf_unique_of_ord_jGeomGen_sub_eq_one
    (q : ℕ) (k : Type*) [Field k] [Fact q.Prime] [CharP k q] [IsAlgClosed k]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (data : ModularPolynomialData N)
    (v : Place k ↥(modularFunctionFieldC k N)) (c : k × k) (hc : IsCentreOf k N c v)
    (huniq : ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v)
    (hord : v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1) :
    (Polynomial.derivative (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval c.1 c.2 ≠ 0 := by sorry
