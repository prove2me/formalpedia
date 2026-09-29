-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_dominantIndices_scale
-- name    : ModularCurve.UVCrossingModel.dominantIndices_scale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/9343e399-6ea2-56a1-b1c3-a96b95da1509
-- title:
--   Scaling invariance of dominant indices under (v,E,t)↦(qv,qE,qt)
-- statement:
--   Let $W$ be a commutative ring, let $v : W \to \mathbb{N}\cup\{\infty\}$ be an arbitrary function, let $E$, $t$ and $q$ be natural numbers with $1 \le q$, and let $ab = (a,b)$ be a pair of one-variable power series over $W$. For given data $(v,E,t)$ the set $\mathrm{dominantIndices}\,v\,E\,t\,ab \subseteq \mathbb{Z}$ consists of those $n$ for which the term order $v(\mathrm{nfCoeff}\,ab\,n) + \mathrm{annulusWeight}\,E\,t\,(\mathrm{nfExponent}\,n)$, computed in $\mathbb{N}\cup\{\infty\}$, equals $\mathrm{repGaussOrder}\,v\,E\,t$ of the two-variable power series $\mathrm{inU}(a) + \mathrm{inV}(b)$, that is, the infimum over all multi-indices $d : \mathrm{Fin}\,2 \to_{f} \mathbb{N}$ of $v$ of the coefficient of $d$ in that series plus $\mathrm{annulusWeight}\,E\,t\,d$. The assertion is that replacing $v$ by the pointwise product $w \mapsto q\cdot v(w)$ and the pair $(E,t)$ by $(qE,qt)$ leaves this set unchanged: $\mathrm{dominantIndices}\,(q\cdot v)\,(qE)\,(qt)\,ab = \mathrm{dominantIndices}\,v\,E\,t\,ab$ as subsets of $\mathbb{Z}$.
--
--   The statement is the compatibility needed to pass between depths measured on an integral grid and rational depths $t/q$ on the annulus attached to a crossing model $W[[U,V]]/(UV-\pi)$: at a grid point the rescaled data $(qv,qE,qt)$ and the original data $(v,E,t)$ single out the same dominant terms of a normal form. It is used by the results computing the order of a residue on such an annulus as the infimum or the supremum of the dominant index set, and by the factorisation of an element with coinciding infimum and supremum as a unit times a monomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_dominantIndices_scale.lean

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

theorem ModularCurve.UVCrossingModel.dominantIndices_scale
    {W : Type u} [CommRing W] (v : W → ℕ∞) (E t q : ℕ) (hq : 1 ≤ q) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab = dominantIndices v E t ab := by sorry
