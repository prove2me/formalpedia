-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_succ_sub_eq_sInf_dominantIndices
-- name    : ModularCurve.UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/aed25075-b793-58b8-9dfd-d59e4aebf833
-- title:
--   Right slope of the Gauss order at depth p
-- statement:
--   Let $W$ be a complete discrete valuation domain (complete with respect to its maximal ideal), let $\varpi \in W$ be irreducible, and let $e, q \ge 1$ be natural numbers. Throughout, the coefficient valuation used is $v(w) = q \cdot \operatorname{addVal}_W(w)$, with values in $\mathbb{N} \cup \{\infty\}$. Let $x$ be a nonzero element of the crossing model $\mathrm{MvPowerSeries}(\mathrm{Fin}\,2, W)/(X_0X_1 - C(\varpi^e))$, and let $ab = (a,b)$ be a pair of one-variable power series over $W$ with $b$ of zero constant term, such that the class of $\mathrm{inU}(a) + \mathrm{inV}(b)$ equals $x$; here $\mathrm{inU}(a)$ is the two-variable series whose coefficient at a multi-degree $d$ is the $d_0$-th coefficient of $a$ when $d_1 = 0$ and $0$ otherwise, and $\mathrm{inV}(b)$ is defined symmetrically. Let $p$ be a natural number with $p+1 \le qe$. For a depth index $t$, the dominant indices $D(t) \subseteq \mathbb{Z}$ of $ab$ are those $n$ for which $v(\mathrm{nfCoeff}\,ab\,n) + \mathrm{annulusWeight}\,(qe)\,t\,(\mathrm{nfExponent}\,n)$ attains the value $\mathrm{repGaussOrder}$ of $\mathrm{inU}(a)+\mathrm{inV}(b)$ at $(qe, t)$, the latter being the infimum over multi-degrees $d$ of $v(\text{coefficient at } d) + \mathrm{annulusWeight}\,(qe)\,t\,d$; and $G(t) = \mathrm{gaussOrder}$ of $x$ at $(qe, t)$ is the supremum of $\mathrm{repGaussOrder}$ at $(qe,t)$ over all two-variable series representing $x$. Assume $\inf D(p) \in D(p+1)$. Then, as integers, $G(p+1) - G(p) = \inf D(p)$, the Gauss orders being converted to natural numbers via `toNat`.
--
--   This is one step of the interior slope law for the Gauss order on the annulus of a width-$e$ node: under the no-kink condition that the least dominant index at depth $p$ remains dominant at depth $p+1$, the right-hand secant slope of $p \mapsto G(p)$ equals that least dominant index. It feeds the integral slope bookkeeping used in the counting identities for circle indices and in the companion results on the extremal dominant indices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_gaussOrder_succ_sub_eq_sInf_dominantIndices.lean

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

theorem ModularCurve.UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hpe : p + 1 ≤ q * e)
    (hright : sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) ∈ dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p + 1) ab) :
    ((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ) - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat = sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) := by sorry
