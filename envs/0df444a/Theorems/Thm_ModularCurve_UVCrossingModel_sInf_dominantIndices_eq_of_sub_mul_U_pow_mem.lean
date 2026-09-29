-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem
-- name    : ModularCurve.UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/e9656c2b-1ed6-51ab-8d94-6b9fb1197d29
-- title:
--   Gauss order vanishes and least dominant index equals m
-- statement:
--   Let $W$ be a commutative domain which is a discrete valuation ring, complete for the adic topology of its maximal ideal, let $\varpi \in W$ be irreducible, and let $e, q \ge 1$ be natural numbers. Work with the valuation $v(w) = q \cdot \mathrm{addVal}_W(w)$, valued in $\mathbb{N}\cup\{\infty\}$, and with the crossing model $R = \mathrm{UVCrossingModel}\,W\,(\varpi^e) = W[[X_0,X_1]]/(X_0X_1 - \varpi^e)$, whose quotient map is `mk (ϖ ^ e)`. Let $x \in R$ be nonzero, let $(a,b)$ be a pair of one-variable power series over $W$ with $b$ of zero constant term, and assume that $x$ is the class of the two-variable series $\mathrm{inU}(a) + \mathrm{inV}(b)$, i.e. of the series whose coefficient at $(i,0)$ is the $i$-th coefficient of $a$, whose coefficient at $(0,j)$ is the $j$-th coefficient of $b$, and which vanishes at mixed exponents. Assume further that for some unit $\gamma$ of $R$ and some $m \in \mathbb{N}$ one has $x - \gamma\,U^m \in (\varpi, V)R$, where $U$, $V$ are the two coordinates `U (ϖ ^ e)`, `V (ϖ ^ e)` of the crossing model and $\varpi$ is taken as the constant `const (ϖ ^ e) ϖ`. Then two things hold simultaneously. First, the Gauss order of $x$ for the weight data $(q e, 0)$ is $0$: the supremum, over all two-variable series $F$ with class $x$, of $\inf_{d} \bigl(v(\mathrm{coeff}_d F) + \mathrm{annulusWeight}\,(qe)\,0\,d\bigr)$ equals $0$. Second, the infimum in $\mathbb{Z}$ of the set of dominant indices of $(a,b)$ for the same data — those $n \in \mathbb{Z}$ for which $v(\mathrm{nfCoeff}\,(a,b)\,n) + \mathrm{annulusWeight}\,(qe)\,0\,(\mathrm{nfExponent}\,n)$ attains the infimum $\inf_d\bigl(v(\mathrm{coeff}_d(\mathrm{inU}(a)+\mathrm{inV}(b))) + \mathrm{annulusWeight}\,(qe)\,0\,d\bigr)$ — equals $m$.
--
--   The statement identifies, at the end of the annulus where the second branch $(\varpi, V)$ is contracted, the normalisation of the Gauss-order polygon (its value $0$) together with its extreme dominant index, which is the order $m$ at the node of the reduction of $x$ along that branch. It is used by the results computing the order of a residue on a node annulus in terms of the infimum or supremum of the dominant indices, and in turn by the construction of component charts and attached annuli for prolongation tuples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (γ : UVCrossingModel W (ϖ ^ e)) (hγ : IsUnit γ) (m : ℕ)
    (hxγ : x - γ * U (ϖ ^ e) ^ m ∈ Ideal.span {const (ϖ ^ e) ϖ, V (ϖ ^ e)}) :
    gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 0 x = 0 ∧
      sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab) = (m : ℤ) := by sorry
