-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_mem_integers_residue_ne_zero_of_qCoeff
-- name    : ModularCurve.MultCovering.infChart_mem_integers_residue_ne_zero_of_qCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/f483db23-e2cf-5e7f-be5f-5227287f1ca5
-- title:
--   q-expansion unit criterion on the ∞̄-chart
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k = \mathrm{ResidueField}(A)$ has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, that is: modular polynomial data for $p$ satisfying the Kronecker congruence $\Phi \bmod p = (X'^p - X)(X' - X^p)$, integrality of the Hecke maps $\bar\alpha$, $\bar\beta$ at level $1$ over $\overline{\mathbb Q}$, a place specialisation $P$ along the residue map $A \to k$, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of the base-changed modular function field $\mathrm{modularFunctionFieldBar}(1\cdot p)$, a finite set $W_n$ of places of $\mathrm{modularFunctionFieldC}\,k\,1$ consisting exactly of the supersingular places $\mathrm{ssPlaces}\,p\,1\,k$, finiteness of the supersingular $j$-set together with the count $\mathrm{mAnnuli}\,p$, and a chart supply for $R$ and $S_1$. Let $f$ be an element of $\mathrm{modularFunctionFieldBar}(1\cdot p)$ whose Laurent coefficients $\mathrm{coeff}_n(f)$ all lie in $A$, and assume some coefficient $\mathrm{coeff}_n(f)$ is a unit of $A$. Then $f$ lies in the valuation subring $(\mathrm{infChart}\,\Gamma).\mathrm{integers}$ of the component chart attached to $\Gamma$, and its image under the residue homomorphism $(\mathrm{infChart}\,\Gamma).\mathrm{residue}$ into $\mathrm{modularFunctionFieldC}\,k\,1$ is non-zero.
--
--   This is the criterion that a $q$-expansion with coefficients in $A$ and at least one unit coefficient is a unit-like element of the $\bar\infty$-chart of the multiplicative covering of $X_0(p)$ at $p$: it is integral there and reduces to a non-zero function on the corresponding component. It belongs to the exported interface of `infChart` and is used in the construction of a uniform multiplicative covering with a certified family for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_mem_integers_residue_ne_zero_of_qCoeff.lean

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

theorem ModularCurve.MultCovering.infChart_mem_integers_residue_ne_zero_of_qCoeff {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (f : ↥(modularFunctionFieldBar (1 * p))) (hf : ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A)
    (hu : ∃ n : ℤ, IsUnit (⟨(f : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hf n⟩ : ↥A)) :
    ∃ h : f ∈ (infChart Γ).integers, (infChart Γ).residue ⟨f, h⟩ ≠ 0 := by sorry
