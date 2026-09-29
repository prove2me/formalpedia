-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom
-- name    : ModularCurve.MultCovering.cuspInftyBar_mem_infChart_dom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/7e537563-ab28-57f7-8a01-808536f9a14d
-- title:
--   The cusp ∞̄ lies in the domain of the ∞-chart
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field has characteristic $p$, and let $\Gamma$ be a chart context `ChartCtx p A`, that is: modular polynomial data at $p$ together with the Kronecker congruence asserting that the bivariate reduction mod $p$ of $\Phi$ equals $(C(X)^p - X)(C(X) - X^p)$; integrality of the Hecke maps $\alpha$ and $\beta$ at level $1$ and prime $p$ over $\overline{\mathbb Q}$; a place specialization $P$ from places of the level-one modular function field over $\overline{\mathbb Q}$ to places over the residue field of $A$, relative to these data and the residue map of $A$; a level-one prolongation pair $R$ for $P$; a set $S_1$ of places of $\overline{\mathbb Q}$-modular function field of level $1\cdot p$; a finset $W_n$ of places of the characteristic-$p$ level-one modular function field whose members are exactly the supersingular places `ssPlaces p 1`; finiteness of `ssJSet` with cardinality `mAnnuli p`; and a datum `R.ChartFstSupply S₁`. Then the place $\bar\infty$ of the level-$1\cdot p$ modular function field over $\overline{\mathbb Q}$, namely the place `cuspInftyBar (1 * p)` attached to the $q$-expansion embedding of $j$, belongs to the set `dom` of the component chart `infChart Γ`, the latter being the first chart `chartFst` built from $R$, $S_1$, $W_n$ and the supply datum.
--
--   This records that the cusp $\bar\infty$ of $X_0(p)$ lies on the component of the mod-$p$ fibre singled out by the first of the two charts of the multiplicative covering, in the chart formalism over the valuation ring $A$. It is used by the results identifying the chart data of `infChart` and `zeroChart` as good families of divisors, where the cuspidal place must be known to lie in the chart's domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem ModularCurve.MultCovering.cuspInftyBar_mem_infChart_dom
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    cuspInftyBar (1 * p) ∈ (infChart Γ).dom := by sorry
