-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_residue_ne_zero_iff_exists_quotient
-- name    : ModularCurve.MultCovering.infChart_residue_ne_zero_iff_exists_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/7bddef63-61e5-51fc-ba73-16bc4bf4e513
-- title:
--   Nonzero ∞̄-chart residue as quotient of A-integral expansions
-- statement:
--   Fix a prime $p$ (as a `Fact`) and a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose residue field has characteristic $p$ and carries decidable equality. Let $\Gamma$ be a chart context `ChartCtx p A`, that is, a package consisting of modular polynomial data for $p$ satisfying the Kronecker congruence, integrality of the level-one Hecke maps $\bar\alpha$ and $\bar\beta$ over $\overline{\mathbb{Q}}$ at $p$, a place specialisation $P$ from places of the base-changed modular function field of level $1$ to places of the level-one function field over the residue field of $A$ together with its reduction map, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of $\overline{\mathbb{Q}}$-base-changed modular functions of level $1\cdot p$, a finite set $W_n$ of places over the residue field which is exactly the set of supersingular places, the finiteness of the supersingular $j$-set together with the assertion that its cardinality equals `mAnnuli p`, and a first-chart supply datum for $R$ and $S_1$. Let $f$ be an element of `modularFunctionFieldBar (1 * p)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot p$ inside Laurent series. The assertion is the equivalence: $f$ lies in the valuation subring of integers of the component chart `infChart Γ` and its image under that chart's residue homomorphism is nonzero, if and only if there are Laurent series $x,y$ with coefficients in $A$ whose coefficientwise reductions to the residue field of $A$ are both nonzero and such that, inside Laurent series over $\overline{\mathbb{Q}}$, $f$ times the image of $y$ equals the image of $x$.
--
--   This is the unit criterion on the $\bar\infty$-chart of the multiplicative covering of the modular curve of level $p$: an element of the function field is a unit of the chart, in the sense of being integral with nonzero residue, exactly when it is a ratio of two $q$-expansions with coefficients in $A$ both of which stay nonzero after reduction. It belongs to the exported interface of the chart and is used in the construction of a uniform multiplicative covering with a certified family for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_residue_ne_zero_iff_exists_quotient.lean

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

theorem ModularCurve.MultCovering.infChart_residue_ne_zero_iff_exists_quotient {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (f : ↥(modularFunctionFieldBar (1 * p))) :
    (∃ h : f ∈ (infChart Γ).integers, (infChart Γ).residue ⟨f, h⟩ ≠ 0) ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) x ≠ 0 ∧ coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by sorry
