-- Prove2me | Theorems.Thm_ModularCurve_SSCarrier_lead_qP_mul_thetaL_zpow_ne_zero
-- name    : ModularCurve.SSCarrier.lead_qP_mul_thetaL_zpow_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/341f3f6c-14c3-58b8-819c-4a3ac1b6e58a
-- title:
--   Non-vanishing leading coefficient of b at supersingular places
-- statement:
--   Let $p$ be a prime with $5 \le p$ and let $K$ be an algebraically closed field of characteristic $p$ with decidable equality, and let $N \ge 1$ be such that $N \ne 0$ in $K$. Work in the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\,K\,N$, the intermediate field of the Laurent series field $\mathrm{LaurentSeries}\,K$ generated over $K$ by the two series $\mathrm{jqModC}\,K$ (the $q$-expansion $q^{-1}\cdot\mathrm{jNum}$ of $j$, base-changed to $K$) and its $N$-th expansion $\mathrm{jqNModC}\,K\,N$. Let $b$ be an element of that field whose underlying Laurent series is $\mathrm{qP}\,K\cdot\bigl(\theta\,\mathrm{jqModC}\,K\bigr)^{-\lfloor (p+1)/2\rfloor}$, where $\mathrm{qP}\,K$ is the reduction to $K$ of the integral power series with constant coefficient $1$ and $n$-th coefficient $-24\sum_{d\mid n} d$ for $n \ge 1$, and $\theta f = q\,\frac{df}{dq}$ (multiplication by $\mathrm{single}\,1\,1$ applied to the Laurent-series derivative). Let $x$ be an element of $\mathrm{SSIndex}\,p\,N\,K$ at weight $k = p+1$, i.e. a place $x$ of the function field over $K$ lying in $\mathrm{ssPlaces}\,p\,N\,K$ (a supersingular place in the sense of the predicate $\mathrm{IsSupersingularPlace}$) together with the data $2 \le p+1$, $2 \mid p+1$, $\mathrm{placeWidth}\,N\,x \mid (p+1)/2$ and $5 \le p$. Then the leading coefficient $\mathrm{lead}\,N\,K\,x\,a\,b = x\bigl(\pi^{a}\,b\bigr)$, where $a = \mathrm{poleOrder} = \bigl(((p+1)/2)\,(\mathrm{jWidth}(x(j))-1)\bigr)/\mathrm{placeWidth}\,N\,x$ (integer division), $\pi$ is the chosen uniformiser at $x$ (an element of valuation $1$) and $x(\cdot)$ denotes evaluation at the place in the residue field $K$, is non-zero.
--
--   This is the statement that the mod-$p$ form $B = E_{p+1} \bmod p = \partial A$, realised as the function $b$ with $q$-expansion $\tilde P\,(\theta\bar\jmath)^{-(p+1)/2}$, has non-zero leading coefficient in the weight-$(p+1)$ coordinate at every supersingular place; equivalently, $b$ has exact pole order $\mathrm{poleOrder}$ there. It is what makes multiplication by $b$ an isomorphism between supersingular carriers in weights $k$ and $k+p+1$, and it is used in the construction of the Hecke action on supersingular carriers and in the compatibility of that action with multiplication by $b$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSCarrier_lead_qP_mul_thetaL_zpow_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_SwdAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSCarrier.lead_qP_mul_thetaL_zpow_ne_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0)
    (b : ↥(modularFunctionFieldC K N))
    (hb : (b : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)))
    (x : ModularCurve.SSIndex p N K hp5 ((p : ℤ) + 1)) :
    ModularCurve.lead N K x.1 (ModularCurve.poleOrder p N K hp5 ((p : ℤ) + 1) x) b ≠ 0 := by sorry
