-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom
-- name    : ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/2839ba3d-d309-53be-a956-d0bc0f77bb7f
-- title:
--   Cross-piece chordal comparison from exhaustive charts and annuli
-- statement:
--   Let $p$ be a prime with $p\ge 5$, let $r$ be a natural number and let $\Phi$ be a good-family context `FamCtx p r` at level $p$ (a `FamData p r` whose tuple $t$ is an embedding basis, normalised so that $t_0=1$, together with the prescribed residue behaviour of $t$ on the $\bar\infty$- and $\bar 0$-charts). Let $s : \mathrm{Fin}\,r \to \overline{\mathcal F}_{1\cdot p}$ be a tuple in the geometric modular function field of level $1\cdot p$ which is an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its span is the Riemann–Roch space $\{f : v(f)\le \exp(D(v))\ \text{for all places } v\}$ of the divisor `embDivisor (1 * p)`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $(p:\overline{\mathbb Q})$ a non-unit of $A$ and residue field of characteristic $p$, let $\Gamma$ be a chart context `ChartCtx p A` and $\Delta$ an annulus context `AnnCtx` over $\Gamma$. Assume exhaustiveness: every place $P$ of $\overline{\mathcal F}_{1\cdot p}$ over $\overline{\mathbb Q}$ (a proper valuation subring containing $\overline{\mathbb Q}$ and a principal ideal ring) lies in the domain of one of the two charts `chart Γ i` ($i=0,1$, namely `infChart Γ` and `zeroChart Γ`) or in the domain of one of the annuli $\Delta.\mathrm{An}\,e$, $e\in\mathrm{Fin}(\mathtt{mAnnuli }p)$. The conclusion: for every non-archimedean absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit disc is exactly $A$ (that is, $a\in A \iff \mu(a)\le 1$), and for all places $P,Q$ that share no chart domain and no annulus domain (for each $i$, $P$ in the domain of `chart Γ i` implies $Q$ is not, and likewise for each $\Delta.\mathrm{An}\,e$), if the evaluation vectors are non-proportional, in the sense that $\mathrm{evalVec}\,s\,P\,i'\cdot \mathrm{evalVec}\,s\,Q\,j' \ne \mathrm{evalVec}\,s\,P\,j'\cdot\mathrm{evalVec}\,s\,Q\,i'$ for some $i',j'$, then the chordal proximity
--   $$\Big|\log \sup_i \mu(x_i) + \log\sup_j\mu(y_j) - \log\sup_{(i,j)}\mu(x_iy_j-x_jy_i)\Big| \le \mathtt{compConst}\,\Phi\,s\,hs\cdot\big(-\log\mu(p)\big),$$
--   where $x=\mathrm{evalVec}\,s\,P$ and $y=\mathrm{evalVec}\,s\,Q$ are the vectors of values at $P$, resp. $Q$, of the coordinates $s_i$ normalised by a pivot coordinate, and the constant is $4\big(\mathtt{linkBudget}\,\Phi\,s\,hs + \mathtt{modulusExp}\big)$.
--
--   This is the cross-piece comparison clause in the construction of a uniform multiplicative covering of $X_0(p)$: it bounds the chordal proximity of two points lying on distinct pieces (charts or annuli) of the covering by a constant multiple of $-\log\mu(p)$, with a constant depending only on the good family and the chosen embedding basis. It is assembled from the corresponding annulus–annulus and annulus–$\bar 0$-chart comparisons together with the $\bar\infty$-chart estimate, and is cited by [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hpart : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), (∃ i, P ∈ (chart Γ i).dom) ∨ (∃ e, P ∈ (Δ.annIn e).dom)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
    (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
    ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
      (∀ i, P ∈ (chart Γ i).dom → Q ∉ (chart Γ i).dom) →
      (∀ e, P ∈ (Δ.annIn e).dom → Q ∉ (Δ.annIn e).dom) →
      (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
      |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
