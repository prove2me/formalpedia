-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul
-- name    : ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/0c0526ad-e57c-52b3-86ce-14cee1aa6913
-- title:
--   Multiplicativity of extreme dominant leading residues
-- statement:
--   Let $W$ be a complete discrete valuation domain (adically complete for its maximal ideal), let $\varpi \in W$ be irreducible and let $e \ge 1$. Put $R = \mathrm{MvPowerSeries}(\mathrm{Fin}\ 2, W)/(X_0X_1 - \varpi^e)$, the crossing model `UVCrossingModel W (ϖ ^ e)`. For a pair $ab = (a,b)$ of one-variable power series, `inU a + inV b` denotes the two-variable series whose coefficient at $d$ is $a_{d_0}$ when $d_1 = 0$ plus $b_{d_1}$ when $d_0 = 0$, and $\mathrm{nfCoeff}\,ab$ is the $\mathbb{Z}$-indexed family $n \mapsto a_n$ for $n \ge 0$, $-(j+1) \mapsto b_{j+1}$. Let $x \ne 0$ and $y \ne 0$ in $R$, with pairs $ab$, $ab'$ whose second components have vanishing constant coefficient and whose associated series reduce to $x$, resp. $y$, in $R$, and let $ab''$ be such a pair reducing to $xy$. For a depth $t$, $\mathrm{dominantIndices}(\mathrm{addVal}\,W, e, t, ab)$ is the set of $n \in \mathbb{Z}$ at which $\mathrm{addVal}\,W(\mathrm{nfCoeff}\,ab\;n) + \mathrm{annulusWeight}\,e\,t\,(\mathrm{nfExponent}\,n)$ equals the infimum $\mathrm{repGaussOrder}$ of $\mathrm{addVal}\,W(\text{coeff}_d) + \mathrm{annulusWeight}\,e\,t\,d$ over all $d$ for `inU ab.1 + inV ab.2`. Writing $\mathrm{LR}(c)$ for $\mathrm{leadingResidue}\,\varpi\,c$, namely $0$ if $c = 0$ and otherwise the residue class of the unit part of $c$ with respect to $\varpi$, the conclusion is the conjunction $\mathrm{LR}(\mathrm{nfCoeff}\,ab''\,(\inf \mathrm{dom}_0\,ab'')) = \mathrm{LR}(\mathrm{nfCoeff}\,ab\,(\inf \mathrm{dom}_0\,ab))\cdot \mathrm{LR}(\mathrm{nfCoeff}\,ab'\,(\inf \mathrm{dom}_0\,ab'))$ and the same identity with the infima at depth $0$ replaced by the suprema of the dominant index sets at depth $e$, the infima and suprema being taken in the conditionally complete lattice $\mathbb{Z}$.
--
--   This is the coefficient-level companion, at the two extreme depths $t = 0$ and $t = e$, of the additivity of extreme dominant indices recorded in [`ModularCurve.UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul`](thm.html#ModularCurve.UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul): a Gauss-lemma statement for the crossing model $W[[U,V]]/(UV - \varpi^e)$, asserting that the leading residues of the extreme dominant normal-form coefficients are multiplicative. It is used in the construction of prolongation tuples at a specialised place, where residues of such extreme coefficients are compared along an inertia-stable datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Definitions.Def_ModularCurve_UVCrossingInitialForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (y : UVCrossingModel W (ϖ ^ e)) (hy : y ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (haby : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y)
    (ab'' : PowerSeries W × PowerSeries W) (hb'' : PowerSeries.constantCoeff ab''.2 = 0)
    (habxy : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) = x * y) :
    leadingResidue ϖ (nfCoeff ab'' (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab''))) =
        leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) *
          leadingResidue ϖ (nfCoeff ab' (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab'))) ∧
      leadingResidue ϖ (nfCoeff ab'' (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab''))) =
        leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) *
          leadingResidue ϖ (nfCoeff ab' (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab'))) := by sorry
