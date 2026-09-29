-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add
-- name    : ModularCurve.UVCrossingModel.exists_sInf_sSup_dominantIndices_charpoly_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/3693f2f5-f594-5d3e-8eeb-6f7732a42935
-- title:
--   Dominant indices of χ_U shift those of x
-- statement:
--   Let $W$ be a complete discrete valuation ring (a commutative domain which is a discrete valuation ring and is adically complete for its maximal ideal), let $\varpi \in W$ be irreducible and let $e \ge 1$. Work in the crossing model $R = \mathrm{MvPowerSeries}(\mathrm{Fin}\,2, W)/(X_0X_1 - C(\varpi^e))$, written `UVCrossingModel W (ϖ ^ e)`. Let $x \in R$ be nonzero, and let $ab = (a,b)$ be a pair of one-variable power series with $b$ of zero constant term such that $x$ is the class of $\mathrm{inU}(a) + \mathrm{inV}(b)$, where $\mathrm{inU}(a)$ is the series supported on the first variable with coefficients those of $a$, and $\mathrm{inV}(b)$ likewise on the second. Assume $R/xR$ is a finite free $W$-module whose rank equals $\inf D_{ab}(0) - \sup D_{ab}(e)$, where for a valuation $v : W \to \mathbb{N}^\infty$, a weight parameter $E$ and a depth $t$, $D$ is the set of $n \in \mathbb{Z}$ with $v(\mathrm{nfCoeff}\ ab\ n) + \mathrm{annulusWeight}\ E\ t\ (\mathrm{nfExponent}\ n)$ equal to $\inf_d\, v(\mathrm{coeff}_d(\mathrm{inU}(a)+\mathrm{inV}(b))) + \mathrm{annulusWeight}\ E\ t\ d$, here taken with $v$ the additive valuation `IsDiscreteValuationRing.addVal W`, $E = e$ and $t \in \{0,e\}$. Then there is an integer $n_0$ such that for every $q \ge 1$, with valuation scaled to $q\cdot$`addVal W` and weight parameter $qe$: $\inf$ of the dominant indices of the pair $(\chi, 0)$ at depth $p$ equals $\inf$ of those of $ab$ plus $n_0$ whenever $p + 1 \le qe$, and the corresponding identity holds for $\sup$ whenever $1 \le p \le qe$; here $\chi$ is the characteristic polynomial, viewed as a power series, of multiplication by the class of `U (ϖ ^ e)` on $R/xR$.
--
--   This is the Cayley–Hamilton comparison in the crossing model: the characteristic polynomial of multiplication by the first variable on $R/xR$ has the same extreme dominant indices as $x$ itself, up to one global integer translation, simultaneously at all rational depths $p/q$ of the annulus. It feeds the rank-and-length computation [`ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop`](thm.html#ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop), and relies on the additivity of extreme dominant indices under multiplication recorded in [`ModularCurve.UVCrossingModel.sInf_dominantIndices_mul_and_sSup_dominantIndices_mul`](thm.html#ModularCurve.UVCrossingModel.sInf_dominantIndices_mul_and_sSup_dominantIndices_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.lean

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

theorem ModularCurve.UVCrossingModel.exists_sInf_sSup_dominantIndices_charpoly_eq_add
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    [Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    [Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    (hΔ : (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) : ℤ) =
      sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)) :
    ∃ n₀ : ℤ, ∀ q : ℕ, 1 ≤ q →
      (∀ p : ℕ, p + 1 ≤ q * e →
        sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p
            (((LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e)))).charpoly : PowerSeries W), 0)) =
          sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) + n₀) ∧
      (∀ p : ℕ, 1 ≤ p → p ≤ q * e →
        sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p
            (((LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e)))).charpoly : PowerSeries W), 0)) =
          sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) + n₀) := by sorry
