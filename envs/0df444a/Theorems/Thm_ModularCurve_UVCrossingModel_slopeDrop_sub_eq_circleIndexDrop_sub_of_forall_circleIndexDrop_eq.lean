-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq
-- name    : ModularCurve.UVCrossingModel.slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/0856609e-24e8-5f4b-909b-fba60fe55bc2
-- title:
--   Two-element slope law on the crossing-model annulus
-- statement:
--   Let $W$ be a complete discrete valuation ring (a commutative domain that is a discrete valuation ring and is adically complete for its maximal ideal), let $\varpi \in W$ be irreducible, and let $e, q \ge 1$ be naturals. Throughout, the weight data are the valuation $w \mapsto q\cdot\mathrm{addVal}_W(w)$ with values in $\mathbb{N}\cup\{\infty\}$ and the exponent bound $E = qe$; for a pair $ab = (a,b)$ of power series, `dominantIndices` is the set of $n \in \mathbb{Z}$ at which the term order $q\,\mathrm{addVal}_W(\mathrm{nfCoeff}\,ab\,n) + \mathrm{annulusWeight}\,E\,t\,(\mathrm{nfExponent}\,n)$ attains the infimal value $\mathrm{repGaussOrder}$ of $\mathrm{inU}\,a + \mathrm{inV}\,b$, and `circleIndexDrop` is $\sup - \inf$ of that set, truncated to $\mathbb{N}$. Let $x, x'$ be nonzero elements of the crossing model $W[[X_0,X_1]]/(X_0X_1 - \varpi^e)$, presented as $x = \mathrm{mk}(\mathrm{inU}\,a + \mathrm{inV}\,b)$ and $x' = \mathrm{mk}(\mathrm{inU}\,a' + \mathrm{inV}\,b')$ with $b, b'$ of vanishing constant coefficient. Assume that for all naturals $r \ge 1$ and $s$ with $r \nmid s$ and $0 < s < rqe$, the circle index drops of $ab$ and $ab'$ at scale $rq$ (valuation $rq\cdot\mathrm{addVal}_W$, bound $rqe$, parameter $s$) agree. Writing $\varphi(p) = (\mathrm{gaussOrder}\,p\,x).\mathrm{toNat} - (\mathrm{gaussOrder}\,p\,x').\mathrm{toNat} \in \mathbb{Z}$ for the Gauss orders at scale $q$, bound $qe$ and parameter $p$, the conclusion is the conjunction of: (i) for every natural $p$ with $1 \le p$ and $p+1 \le qe$, $(\varphi(p)-\varphi(p-1)) - (\varphi(p+1)-\varphi(p))$ equals the circle index drop of $ab$ at parameter $p$ minus that of $ab'$; (ii) $\varphi(1)-\varphi(0) = \inf \mathrm{dominantIndices}(0, ab) - \inf \mathrm{dominantIndices}(0, ab')$; and (iii) $\varphi(qe)-\varphi(qe-1) = \sup \mathrm{dominantIndices}(qe, ab) - \sup \mathrm{dominantIndices}(qe, ab')$, all subtractions of naturals being natural subtraction where the arguments are naturals.
--
--   This is the slope law, in the two-element form, for the difference of Gauss orders of two elements of the crossing model $W[[U,V]]/(UV-\varpi^e)$: the hypothesis says that the two elements have equal circle index drops at every parameter off the $1/q$-grid, and the conclusion computes the slope drops of the resulting piecewise-linear function at grid points together with its two end slopes. It is cited by the grid second-difference statements [`ModularCurve.UVCrossingModel.gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq`](thm.html#ModularCurve.UVCrossingModel.gridSecondDiff_eq_circleIndexDrop_sub_of_forall_offGrid_eq) and its scaled variant, on the way to the divisor bookkeeping on the annuli of the crossing model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq.lean

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

theorem ModularCurve.UVCrossingModel.slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (x' : UVCrossingModel W (ϖ ^ e)) (hx' : x' ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (habx' : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = x')
    (hoff : ∀ r s : ℕ, 1 ≤ r → ¬ r ∣ s → 0 < s → s < r * q * e →
        circleIndexDrop (fun w => ((r * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * q * e) s ab =
          circleIndexDrop (fun w => ((r * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * q * e) s ab') :
    (∀ p : ℕ, 1 ≤ p → p + 1 ≤ q * e →
      ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x').toNat)
        - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x').toNat))
      - ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x').toNat)
        - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x').toNat))
      = (circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab : ℤ)
        - circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab') ∧
    ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 1 x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 1 x').toNat)
      - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 0 x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 0 x').toNat)
      = sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab)
        - sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab')) ∧
    ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e) x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e) x').toNat)
      - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e - 1) x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e - 1) x').toNat)
      = sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab)
        - sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab')) := by sorry
