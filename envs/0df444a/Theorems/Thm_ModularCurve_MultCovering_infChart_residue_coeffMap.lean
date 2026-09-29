-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_residue_coeffMap
-- name    : ModularCurve.MultCovering.infChart_residue_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/22910378-65d3-5360-b2ca-2dc56c26fb38
-- title:
--   Residue of an A-integral q-expansion on the ∞̄-chart
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k = \mathrm{ResidueField}(A)$ has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, that is: modular polynomial data for $p$ together with a witness that its reduction satisfies the Kronecker congruence $\bar\Phi = (X_1^p - X_2)(X_1 - X_2^p)$, integrality of the Hecke $\bar\alpha$- and $\bar\beta$-maps at level $1$ for $p$ over $\overline{\mathbb Q}$, a place specialisation $P$ from places of $\overline{F}(1)$ to places of $\mathrm{modularFunctionFieldC}\,k\,1$ reducing along $A \to k$, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of the level-$1\cdot p$ field $\mathrm{modularFunctionFieldBar}(1\cdot p)$, a finset $W_n$ of places of $\mathrm{modularFunctionFieldC}\,k\,1$ enumerating exactly $\mathrm{ssPlaces}\,p\,1\,k$, finiteness of $\mathrm{ssJSet}\,p\,k$ with cardinality $\mathrm{mAnnuli}\,p$, and a chart supply datum for $R$ and $S_1$. Let $y$ be a Laurent series with coefficients in $A$ and assume that its coefficientwise image $\mathrm{coeffMap}(A \hookrightarrow \overline{\mathbb Q})(y)$ lies in $\mathrm{modularFunctionFieldBar}(1\cdot p)$, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1\cdot p$ inside $\mathrm{LaurentSeries}(\overline{\mathbb Q})$. Then this element belongs to the valuation subring `(infChart Γ).integers` of the component chart $\mathrm{infChart}\,\Gamma$, and its image under the chart's residue homomorphism into $\mathrm{modularFunctionFieldC}\,k\,1$ equals, as a Laurent series over $k$, the coefficientwise reduction $\mathrm{coeffMap}(\mathrm{residue}_A)(y)$ of $y$.
--
--   This records the behaviour of the $\bar\infty$-chart of the uniform multiplicative covering of the modular curve of level $p$ on $q$-expansions: the chart's valuation ring contains every $q$-expansion with coefficients in $A$ and its residue map is coefficientwise reduction modulo the maximal ideal of $A$. It belongs to the exported interface of `infChart` and is used in the construction of a uniform multiplicative covering with a certified family for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_residue_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem ModularCurve.MultCovering.infChart_residue_coeffMap {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * p)) :
    ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ (infChart Γ).integers,
      (((infChart Γ).residue ⟨_, hint⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
          LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y := by sorry
