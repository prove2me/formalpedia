-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_residue_jF_jpF
-- name    : ModularCurve.MultCovering.infChart_residue_jF_jpF
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/eb98c5cd-4ef0-5ddb-b375-8227f0a07ffe
-- title:
--   Residues of j and j(qᵖ) on the ∞̄-chart
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $k = \mathrm{ResidueField}\,A$ has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, that is, a package consisting of modular polynomial data for $p$ together with a Kronecker congruence for it, integrality of the Hecke $\bar\alpha$- and $\bar\beta$-maps for level $1$ and prime $p$ over $\overline{\mathbb{Q}}$, a place specialization $P$ from places of the base-changed modular function field of level $1$ to places of the level-$1$ modular function field over $k$ (with reduction the residue map of $A$), a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of the level-$(1\cdot p)$ base-changed modular function field, a finite set $W_n$ of places of the level-$1$ modular function field over $k$ characterised as exactly the supersingular places, a proof that the supersingular $j$-set over $k$ is finite with cardinality $\mathrm{mAnnuli}\,p$, and a chart supply datum for $R$ and $S_1$. Assume moreover $A.\mathrm{LiesOverPrime}\,p$, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$. The conclusion concerns the component chart $\mathrm{infChart}\,\Gamma$, the first chart attached to $\Gamma.R$, $\Gamma.S_1$ and $W_n$: the two elements $jF\,p$ (the coefficient embedding of the $q$-expansion $j(q)$) and $jpF\,p$ (the coefficient embedding of $j(q^p)$) of the level-$(1\cdot p)$ base-changed modular function field both lie in the chart's valuation subring `integers`, and their images under the chart's residue homomorphism into the level-$1$ modular function field over $k$ are, respectively, $\bar\jmath$ (the element given by the series $\mathrm{jqModC}\,k$) and $\bar\jmath^{\,p}$.
--
--   This is the Kronecker congruence $j(q^p) \equiv j(q)^p$ read off on the $\bar\infty$-chart of the multiplicative covering of $X_0(p)$ in characteristic $p$: both $j$ and $j(q^p)$ are chart-integral there, with residues $\bar\jmath$ and $\bar\jmath^{\,p}$. It is the form of the statement used downstream, and is cited by the separate extraction lemmas for the integrality of $jF\,p$ and for each of the two residue identities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_residue_jF_jpF.lean

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

theorem ModularCurve.MultCovering.infChart_residue_jF_jpF {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (hA : A.LiesOverPrime p) :
    ∃ (hj : jF p ∈ (infChart Γ).integers) (hjp : jpF p ∈ (infChart Γ).integers),
      (infChart Γ).residue ⟨jF p, hj⟩ = jBar (IsLocalRing.ResidueField ↥A) ∧
      (infChart Γ).residue ⟨jpF p, hjp⟩ = jBar (IsLocalRing.ResidueField ↥A) ^ p := by sorry
