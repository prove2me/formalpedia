-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_not_isSSCentred_of_mem_infChart_dom
-- name    : ModularCurve.MultCovering.not_isSSCentred_of_mem_infChart_dom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/7917d0cc-211f-5d35-b441-c21beeb21fb5
-- title:
--   No place of the ∞̄-chart domain is supersingular-centred
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k =$ `ResidueField ↥A` has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, i.e. a package consisting of modular polynomial data for $p$ satisfying the Kronecker congruence, integrality of the Hecke $\bar\alpha$- and $\bar\beta$-maps at level $1$ and prime $p$, a place specialisation $P$ from places of $\overline{\mathbb Q}(X_0(1))^- =$ `modularFunctionFieldBar 1` to places of the characteristic-$p$ function field over $k$ along the residue map $A \to k$, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of `modularFunctionFieldBar (1 * p)`, a finite set $W_n$ of places of `modularFunctionFieldC k 1` that is exactly the set of supersingular places `ssPlaces p 1 k`, the finiteness of `ssJSet p k` together with the assertion that its cardinality equals `mAnnuli p`, and a chart-first supply for $R$ over $S_1$. Let $W$ be a place of `modularFunctionFieldBar (1 * p)` over $\overline{\mathbb Q}$ lying in the domain of the component chart `infChart Γ`, which is the chart `chartFst` built from $R$, $S_1$, $W_n$ and the supply, and let $a \in k$ lie in `ssJSet p k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero point killed by $p$. Then `IsSSCentred p A W a` fails: it is not the case that both there exists $x \in A$ with residue $a$ and $W.\mathrm{ord}\bigl(\mathrm{jFun} - x\bigr) > 0$, and there exists $y \in A$ with residue $a^p$ and $W.\mathrm{ord}\bigl(\mathrm{jqFun} - y\bigr) > 0$.
--
--   This is the separation statement for the $\bar\infty$-chart of the uniform multiplicative covering of $X_0(p)$ at $p$: the places in the domain of that chart avoid the supersingular crossing points, where both $j$ and $j_p$ reduce to a supersingular value. It is used in the construction of a uniform multiplicative covering with a certified family for primes $p \ge 5$, via [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_not_isSSCentred_of_mem_infChart_dom.lean

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

theorem ModularCurve.MultCovering.not_isSSCentred_of_mem_infChart_dom {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hW : W ∈ (infChart Γ).dom)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ¬ IsSSCentred p A W a := by sorry
