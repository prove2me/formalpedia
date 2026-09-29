-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff
-- name    : ModularCurve.UVCrossingModel.free_finite_finrank_quotient_span_of_isUnit_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/351915b0-3bb6-5e48-ae35-56d1a57a0703
-- title:
--   Free finite quotient of rank the Gauss polygon drop
-- statement:
--   Let $W$ be a complete discrete valuation ring: a commutative domain which is a discrete valuation ring and is adically complete for its maximal ideal. Let $\varpi \in W$ be irreducible, let $e \ge 1$ be a natural number, and set $R = \mathrm{MvPowerSeries}\,(\mathrm{Fin}\ 2)\ W / (X_0X_1 - \varpi^{e})$, the ring `UVCrossingModel W (ϖ ^ e)`. Let $x \in R$ be nonzero, and let $ab = (a,b)$ be a pair of one-variable power series over $W$ with $b$ of zero constant term, such that $x$ is the class under `mk (ϖ ^ e)` of $\mathrm{inU}\,a + \mathrm{inV}\,b$, where $\mathrm{inU}\,a$ is the two-variable series with coefficient $a_{d_0}$ at $d$ when $d_1 = 0$ and $0$ otherwise, and $\mathrm{inV}\,b$ is the series with coefficient $b_{d_1}$ at $d$ when $d_0 = 0$ and $0$ otherwise. Assume the two goodness hypotheses: some coefficient of $a$ is a unit of $W$, and either the constant coefficient of $a$ is a unit or some coefficient $b_j$ with $j \ge 1$ is a unit. Then $R / \mathrm{span}\{x\}$ is a free and finite $W$-module, and its $W$-rank, viewed in $\mathbb{Z}$, equals $\mathrm{sInf}\,D_0 - \mathrm{sSup}\,D_e$, where for $t \in \{0,e\}$ the set $D_t \subseteq \mathbb{Z}$ is `dominantIndices (addVal W) e t ab`, the set of integers $n$ at which the term order $\mathrm{addVal}_W(\mathrm{nfCoeff}\,ab\,n) + \mathrm{annulusWeight}\,e\,t\,(\mathrm{nfExponent}\,n)$ attains the value `repGaussOrder (addVal W) e t (inU a + inV b)`, itself the infimum over bi-exponents $d$ of $\mathrm{addVal}_W$ of the coefficient at $d$ plus $\mathrm{annulusWeight}\,e\,t\,d$; here $\mathrm{sInf}$ and $\mathrm{sSup}$ are the lattice operations on subsets of $\mathbb{Z}$.
--
--   This is the Weierstrass-type zero-counting statement for the crossing model $W[[U,V]]/(UV - \varpi^{e})$: for a good element $x$, the quotient $R/xR$ is $W$-free of rank the total drop of the Gauss polygon of $x$ between depth $0$ (the branch $V = 0$) and depth $e$ (the branch $U = 0$). It is cited by [`ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop`](thm.html#ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_circleIndexDrop) and by [`ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff`](thm.html#ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff), where the rank is matched with a sum of local contributions along the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.lean

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

theorem ModularCurve.UVCrossingModel.free_finite_finrank_quotient_span_of_isUnit_coeff
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (hgood0 : ∃ i, IsUnit (PowerSeries.coeff i ab.1))
    (hgoodE : IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2)) :
    Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) ∧
    Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) ∧
    ((Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) : ℤ) =
      sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)) := by sorry
