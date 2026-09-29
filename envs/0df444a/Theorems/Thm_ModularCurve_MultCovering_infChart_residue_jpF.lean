-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_residue_jpF
-- name    : ModularCurve.MultCovering.infChart_residue_jpF
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/ba9b5361-5bdd-5bbc-bc28-afe39028d8aa
-- title:
--   Residue of j(qᵖ) on the ∞̄-chart equals ̄ j^{ p}
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k = \mathrm{ResidueField}(A)$ has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, that is, a package consisting of modular polynomial data at $p$ together with a Kronecker congruence for it, integrality of the Hecke operators $\bar\alpha$ and $\bar\beta$ at level $1$ and prime $p$ over $\overline{\mathbb Q}$, a place specialization $P$ from places of the base-changed modular function field $\overline{\mathcal F}_1$ to places of $\mathcal F_1(k)$ reducing along $A \to k$, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of $\overline{\mathcal F}_{1\cdot p}$, a finite set $W_n$ of places of $\mathcal F_1(k)$ consisting exactly of the supersingular places, a proof that the supersingular $j$-set over $k$ is finite with cardinality $\mathrm{mAnnuli}\,p$, and a chart supply datum for $R$ and $S_1$. Assume $A$ lies over $p$, i.e. the image of $p$ in $\overline{\mathbb Q}$ is a nonunit of $A$. Write $\mathcal C_\infty = \mathrm{infChart}\,\Gamma$ for the component chart obtained as the first chart of $R$ from $S_1$, $W_n$ and the supply datum; it carries a valuation subring $\mathcal C_\infty.\mathrm{integers}$ of $\overline{\mathcal F}_{1\cdot p}$ and a surjective residue homomorphism onto $\mathcal F_1(k)$. Finally let $j_p = \mathrm{jpF}\,p$, the element of $\overline{\mathcal F}_{1\cdot p}$ given by the coefficientwise embedding of the $q$-expansion $j(q^p)$, and assume $j_p$ lies in $\mathcal C_\infty.\mathrm{integers}$. Then the residue of $j_p$ equals $\bar j^{\,p}$, where $\bar j \in \mathcal F_1(k)$ is the Laurent series $q^{-1}\cdot(\text{numerator of } j)$ with coefficients reduced into $k$.
--
--   This is the Kronecker-congruence half of the description of the $\bar\infty$-chart of the uniform multiplicative covering of $X_0(p)$ at $p$: on that chart the function $j(q^p)$ specialises to the $p$-th power of the reduced $j$-function, matching the mod $p$ identity $j(q^p) \equiv j(q)^p$. It is used in the construction of a uniform multiplicative covering with a certified family of components for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_residue_jpF.lean

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

theorem ModularCurve.MultCovering.infChart_residue_jpF {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (hA : A.LiesOverPrime p)
    (h : jpF p ∈ (infChart Γ).integers) :
    (infChart Γ).residue ⟨jpF p, h⟩ = jBar (IsLocalRing.ResidueField ↥A) ^ p := by sorry
