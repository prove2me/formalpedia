-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_mem_infChart_integers_iff
-- name    : ModularCurve.MultCovering.mem_infChart_integers_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/3a25eaf9-22b7-588b-99f2-a17dbee6cbab
-- title:
--   Quotient criterion for the ∞̄-chart's valuation ring
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, i.e. a package consisting of modular polynomial data for $p$ satisfying the Kronecker congruence $\Phi \equiv (X'^{\,p}-X)(X'-X^{p})$ modulo $p$, integrality of the two Hecke maps $\bar\alpha,\bar\beta$ at level $1$ and prime $p$, a place specialisation $P$ from places of the level-$1$ function field over $\overline{\mathbb Q}$ to places over the residue field of $A$, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of $\overline{\mathbb Q}$-base-changed modular function field of level $1\cdot p$, a finset $W_n$ of places of the level-$1$ function field over the residue field which is exactly the set of supersingular places, finiteness of the supersingular $j$-set together with the count $m$ of annuli, and a chart-first supply for $R$ and $S_1$. Let $f$ belong to `modularFunctionFieldBar (1 * p)`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1\cdot p$ inside $\overline{\mathbb Q}((q))$. Then $f$ lies in the valuation subring `integers` of the component chart `infChart Γ` if and only if there are Laurent series $x,y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ along $A \to \mathrm{ResidueField}\,A$ is nonzero and $f \cdot y = x$ as Laurent series over $\overline{\mathbb Q}$, the coefficients of $x$ and $y$ being viewed in $\overline{\mathbb Q}$ via the inclusion of $A$.
--
--   This identifies the valuation ring of the $\bar\infty$-chart of the multiplicative covering of $X_0(p)$ at $p$ as the Gauss prolongation of the valuation of $A$ to $q$-expansions at $\infty$: an element is integral precisely when it is a quotient of two Laurent series over $A$ whose denominator has nonzero reduction. It is part of the chart interface used in the construction of a uniform multiplicative covering for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_mem_infChart_integers_iff.lean

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

theorem ModularCurve.MultCovering.mem_infChart_integers_iff {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (f : ↥(modularFunctionFieldBar (1 * p))) :
    f ∈ (infChart Γ).integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by sorry
