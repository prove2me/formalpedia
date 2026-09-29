-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_jF_mem_infChart_integers
-- name    : ModularCurve.MultCovering.jF_mem_infChart_integers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/a311e6bb-5e64-5137-855c-efef87126e1f
-- title:
--   j lies in the integers of the ∞̄-chart
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` whose residue field has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, that is: modular polynomial data for $p$ together with the Kronecker congruence $\mathrm{reduceModBivar}\,p\,\Phi = (C X^p - X)(C X - X^p)$ for it; integrality of the two Hecke ring homomorphisms $\bar\alpha$, $\bar\beta$ at level $1$ and prime $p$ over $\overline{\mathbb Q}$; a place specialization $P$ from places of $\overline{\mathbb Q}$-modular function field $\overline{\mathcal F}_1$ to places of the characteristic-$p$ modular function field over $\mathrm{ResidueField}\,A$, taken along the residue map of $A$; a level-one prolongation pair $R$ for $P$; a set $S_1$ of places of $\overline{\mathcal F}_{1\cdot p}$; a finset $W_n$ of places of the characteristic-$p$ level-one modular function field whose members are exactly the supersingular places `ssPlaces p 1`; finiteness of `ssJSet p` with exactly `mAnnuli p` elements; and a chart supply datum for $R$ and $S_1$. Assume further that $p$, as an element of $\overline{\mathbb Q}$, is a non-unit of $A$. Then `jF p`, the element of $\overline{\mathcal F}_{1\cdot p}$ given by the $q$-expansion of $j$ with coefficients embedded in $\overline{\mathbb Q}$, belongs to the valuation subring `integers` of the component chart `infChart Γ`, the first chart attached to $\Gamma.R$, $\Gamma.S_1$, $W_n$ and the supply datum.
--
--   This records the integrality of the modular invariant $j$ on the $\bar\infty$-component chart of the multiplicative covering of $X_0(p)$ at $p$, i.e. that $j$ lies in the valuation ring cutting out that chart. It is part of the exported interface of that chart and is used in the construction of a uniform multiplicative covering with a certified family for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_jF_mem_infChart_integers.lean

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

theorem ModularCurve.MultCovering.jF_mem_infChart_integers {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (hA : A.LiesOverPrime p) :
    jF p ∈ (infChart Γ).integers := by sorry
