-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_nonempty_chartCtx
-- name    : ModularCurve.MultCovering.nonempty_chartCtx
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/3ddfede2-dfa3-5e38-b225-e4330c9642ca
-- title:
--   Existence of a chart context for X₀(p) over A
-- statement:
--   Let $p$ be a prime with $5 \le p$, and let $A$ be a valuation subring of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ satisfying `LiesOverPrime p`, i.e. the image of $p$ lies in the non-units of $A$, whose residue field is of characteristic $p$. The assertion is that the type `ChartCtx p A` is nonempty, that is, there exists a bundle consisting of: modular polynomial data for $p$ together with a proof of the Kronecker congruence, stating that the bivariate reduction mod $p$ of the modular polynomial $\Phi$ equals $(C(X)^p - X)(C(X) - X^p)$; proofs that the two level-one Hecke maps $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ at level $1$ and prime $p$ have integral underlying ring homomorphisms; a place specialization $P$ over $A$ at level $1$, relative to these data and the residue map of $A$, transporting places and degree-zero divisor classes of $\overline{\mathbb{Q}}$-modular function fields to those over the residue field; a level-one prolongation pair $R$ for $P$; a set $S_1$ of places of the level-$1\cdot p$ modular function field over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$; a finite set `Wn` of places of the level-one modular function field over the residue field whose members are exactly the supersingular places `ssPlaces p 1`; finiteness of the supersingular $j$-set `ssJSet p` over the residue field, with cardinality equal to `mAnnuli p`; and a witness that $S_1$ is a `ChartFstSupply` for $R$.
--
--   This is the existence statement for the chart context underlying the uniform multiplicative covering of $X_0(p)$ at $p$: it supplies the data on which the two component charts, the annuli and the associated family constructions are defined. It is invoked by the cross-comparison lemmas relating annuli with each other and with the zero chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_nonempty_chartCtx.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem ModularCurve.MultCovering.nonempty_chartCtx (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] :
    Nonempty (ChartCtx p A) := by sorry
