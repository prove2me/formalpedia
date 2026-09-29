-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_jpF_mem_infChart_integers
-- name    : ModularCurve.MultCovering.jpF_mem_infChart_integers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/f9335ac4-b3f7-5147-8272-99c8f482528d
-- title:
--   j(qᵖ) lies in the ∞̄-chart's valuation ring
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field has characteristic $p$. Let $\Gamma$ be a chart context for $p$ and $A$, that is: modular polynomial data for $p$ satisfying the Kronecker congruence $\Phi_p \equiv (X'^p - X)(X' - X^p)$ modulo $p$; the integrality of the two Hecke ring homomorphisms $\alpha$, $\beta$ in level $1$ over $\overline{\mathbb{Q}}$; a place specialisation $P$ from places of the level-$1$ modular function field over $\overline{\mathbb{Q}}$ to places of the corresponding field over the residue field of $A$; a level-one prolongation pair $R$ for $P$; a set $S_1$ of places of the level-$p$ function field $\overline{\mathbb{Q}}$-extension; a finset $W_n$ of places of the residual level-$1$ function field which is exactly the set of supersingular places; the finiteness of the supersingular $j$-set together with the statement that its cardinality equals the number $m$ of annuli; and a chart first supply for $R$ and $S_1$. Assume further that $A$ lies over $p$, i.e. $p$ is a non-unit of $A$. Then the element $j(q^p)$ of the level-$p$ function field — the image under the coefficient embedding of the $q$-expansion $q \mapsto q^p$ applied to $j$ — lies in the valuation subring `integers` of the component chart $\mathrm{infChart}\,\Gamma$, which is the first chart attached to the pair $R$ by the data $S_1$, $W_n$ and the supply.
--
--   This records one half of the integrality statement for the $\bar\infty$-chart of the multiplicative covering of $X_0(p)$ at $p$: both $j$ and $j(q^p)$ are regular there, with residues $\tilde\jmath$ and $\tilde\jmath^{\,p}$. It is part of the exported interface of that chart and is used in the construction of a uniform multiplicative covering with a certified family for primes $p \geq 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_jpF_mem_infChart_integers.lean

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

theorem ModularCurve.MultCovering.jpF_mem_infChart_integers {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (hA : A.LiesOverPrime p) :
    jpF p ∈ (infChart Γ).integers := by sorry
