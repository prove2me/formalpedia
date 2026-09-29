-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
-- name    : ModularCurve.MultCovering.mem_zeroChart_nodes_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/4da16968-3ebe-56f1-9c1c-ce619cb6eba3
-- title:
--   Nodes of the Fricke-transported chart: ̃ j = aᵖ supersingular
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $k = \mathrm{ResidueField}\,A$ has characteristic $p$, and a chart context $\Gamma$ of type `ChartCtx p A`; the latter packages modular polynomial data together with the Kronecker congruence for it, integrality of the Hecke operators $\bar\alpha$, $\bar\beta$ at level $1$ and prime $p$ over $\overline{\mathbb Q}$, a place specialisation $P$ of $A$ above level $1$ with residue map to $k$, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of the geometric modular function field of level $1\cdot p$, a finite set $\mathrm{Wn}$ of places of $k(\tilde j) =$ `modularFunctionFieldC k 1` over $k$ consisting exactly of the supersingular places `ssPlaces p 1 k`, the finiteness of `ssJSet p k` together with the equality of its cardinality with `mAnnuli p`, and a supply datum for the first chart of $R$ relative to $S_1$. Let $x$ be a place of $k(\tilde j)$ over $k$, i.e. a valuation subring of `modularFunctionFieldC k 1` containing $k$, proper, and a principal ideal ring. The assertion is that $x$ belongs to the finite node set of `zeroChart Γ`, the component chart obtained from `infChart Γ` by transport along the Fricke involution of the level-$1\cdot p$ geometric modular function field, if and only if there is an $a \in$ `ssJSet p k` with $x =$ `charLGeomPlaceOfPoint k (a ^ p)`, the place of $k(\tilde j)$ attached to the linear polynomial $\tilde j - a^{p}$. Here `ssJSet p k` is the set of $j \in k$ such that every elliptic Weierstrass curve $W$ over $k$ with $W.j = j$ has no nonzero affine point killed by $p$.
--
--   This identifies the crossing points of the second component of the mod-$p$ model of $X_0(p)$ (the component obtained from the first by the Fricke involution $w_p$) as the places $\tilde j = a^{p}$ with $a$ a supersingular invariant, the Frobenius twist of the indexing used on the first component. It is the indexing statement behind the subsequent analysis of the supersingular annuli, and is used in the construction of Hasse-exponent and width data for the multiplicative covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.mem_zeroChart_nodes_iff {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (x : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
    x ∈ (zeroChart Γ).nodes ↔
      ∃ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A), charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p) = x := by sorry
