-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_not_isSSCentred_of_mem_zeroChart_dom
-- name    : ModularCurve.MultCovering.not_isSSCentred_of_mem_zeroChart_dom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/2215482c-614e-5c79-b28c-f00b2ed981f7
-- title:
--   Places in the zero chart are never supersingularly centred
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k = \mathrm{ResidueField}(A)$ has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, i.e. the package consisting of modular polynomial data for $p$ satisfying the Kronecker congruence, integrality of the base-changed Hecke operators $\alpha,\beta$ at level $1$ and prime $p$, a place specialisation $P$ over $A$ together with a level-one prolongation pair $R$, a set $S_1$ of places of $\overline{\mathbb Q}(X(1\cdot p))$, a finset $W_n$ of places of the level-one function field over $k$ which is exactly the set of supersingular places, the finiteness of the supersingular $j$-set of $k$ with cardinality $\mathrm{mAnnuli}\,p$, and a supply datum `R.ChartFstSupply S₁`. Let $W$ be a place of $\mathrm{modularFunctionFieldBar}(1\cdot p)$ over $\overline{\mathbb Q}$ (a proper valuation subring containing the image of the base field and a principal ideal ring), lying in the domain of `zeroChart Γ`, that is, the translate of $W$ by the Fricke involution $\mathrm{frickeInvolutionBar}(1\cdot p)$ lies in the domain of the chart $\mathrm{infChart}\,\Gamma$. Let $a \in k$ lie in $\mathrm{ssJSet}\,p\,k$, meaning that every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero point killed by $p$. Then `IsSSCentred p A W a` fails: it is not the case that both there is $x \in A$ with residue $a$ and $\mathrm{ord}_W(\mathrm{jFun} - x) > 0$, and there is $y \in A$ with residue $a^p$ and $\mathrm{ord}_W(\mathrm{jqFun} - y) > 0$.
--
--   This is the zero-component half of the disjointness of the chart domains of the two-component covering of $X_0(p)$ over $A$ from the supersingular crossings: no place in the domain of the chart obtained by transporting the $\infty$-chart along the Fricke involution is centred at a supersingular crossing. It feeds the partition clause of the uniform multiplicative covering theorem [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_not_isSSCentred_of_mem_zeroChart_dom.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.not_isSSCentred_of_mem_zeroChart_dom {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))
    (hW : W ∈ (zeroChart Γ).dom) (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ¬ IsSSCentred p A W a := by sorry
