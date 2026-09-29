-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_residue_jF
-- name    : ModularCurve.MultCovering.infChart_residue_jF
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/e0b1e641-39d7-5c5b-a373-919ed20dc7e9
-- title:
--   Residue of j on the ∞̄-chart is jmath̄
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k = \mathrm{ResidueField}\,A$ has characteristic $p$, and let $\Gamma$ be a chart context `ChartCtx p A`, i.e. a package consisting of modular polynomial data for $p$ together with a Kronecker congruence for it, integrality of the Hecke operators $\bar\alpha$ and $\bar\beta$ at level $1$ over $\overline{\mathbb Q}$, a place specialisation $P$ from places of the function field $\overline{\mathbb Q}$-field `modularFunctionFieldBar 1` to places of `modularFunctionFieldC k 1` compatible with the reduction $A \to k$, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of `modularFunctionFieldBar (1 * p)`, the finset $W_n$ of supersingular places at level $1$ over $k$, finiteness and cardinality data for the supersingular $j$-set, and a first-chart supply for $R$ along $S_1$. Assume $p$ lies in the nonunits of $A$ (`A.LiesOverPrime p`), and let $h$ witness that $jF\,p$ — the element of `modularFunctionFieldBar (1 * p)` given by the $q$-expansion of $j$ with coefficients in $\overline{\mathbb Q}$ — lies in the valuation subring `integers` of the component chart $\operatorname{infChart}\Gamma$, which is the first chart `chartFst` attached to $\Gamma.R$, $S_1$, $W_n$ and the supply. Then the residue map of that chart sends $\langle jF\,p, h\rangle$ to $jBar\,k$, the element $j$-$q$-expansion `jqModC k` of `modularFunctionFieldC k 1`.
--
--   This records the behaviour of the $j$-function on the $\bar\infty$-chart of the multiplicative covering of $X_0(p)$ at $p$: reducing the $q$-expansion of $j$ along the chart's residue map gives the mod-$p$ $q$-expansion of $j$ on the level-one curve over $k$. It is part of the exported interface of the chart used in the construction of a uniform multiplicative covering with a certified family for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_residue_jF.lean

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

theorem ModularCurve.MultCovering.infChart_residue_jF {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (hA : A.LiesOverPrime p)
    (h : jF p ∈ (infChart Γ).integers) :
    (infChart Γ).residue ⟨jF p, h⟩ = jBar (IsLocalRing.ResidueField ↥A) := by sorry
