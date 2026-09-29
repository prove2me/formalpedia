-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one
-- name    : ModularCurve.MultCovering.abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/a3b53088-cd69-51de-9089-a7c1dad5cc9c
-- title:
--   Proximity bound at an ∞̄-chart place against a small place
-- statement:
--   Fix a prime $p$ with $5 \le p$ and $r \in \mathbb{N}$. Let $\Phi$ be a good-family context `FamCtx p r`, with members $t_i =$ `goodFamily Φ i` in the geometric modular function field $\overline{\mathcal F}_{1\cdot p}$, and let $s : \mathrm{Fin}\,r \to \overline{\mathcal F}_{1\cdot p}$ be an embedding basis, i.e. linearly independent over $\overline{\mathbb Q}$ and spanning the Riemann–Roch space of the embedding divisor of level $1\cdot p$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ in its nonunits, with residue field of characteristic $p$, let $\Gamma$ be a chart context `ChartCtx p A`, and let $\mu$ be a non-archimedean absolute value on $\overline{\mathbb Q}$ whose unit ball is exactly $A$. Assume: every $t_i$ lies in the integers of the chart `infChart Γ`; a pivot assignment $c_Q$ sending each place of $\overline{\mathcal F}^{\,C}_1$ over the residue field of $A$ to an index in $\mathrm{Fin}\,r$; every place $P$ in the domain of `infChart Γ` is rational (the structure map from $\overline{\mathbb Q}$ onto its residue field is surjective); for all such $P$ and all $j$ the ratio $t_j\,t_{c_Q(\bar P)}^{-1}$, where $\bar P$ is the image of $P$ under the chart's place map, lies both in the chart's integers and in the valuation subring of $P$; and for each such $P$ there is an index $l$ with $1 \le l$ and $\mu\big(P(t_l t_{c_Q(\bar P)}^{-1})\big) = 1$, the evaluation being residue followed by the inverse of the structure map. The conclusion: for every $P$ in the domain of `infChart Γ` and every rational place $Q$ of $\overline{\mathcal F}_{1\cdot p}$ over $\overline{\mathbb Q}$ such that for all $l$ with $1 \le l$ one has $t_l$ in the valuation subring of $Q$ and $\mu(Q(t_l)) < 1$, if the evaluation vectors `evalVec s P` and `evalVec s Q` (coordinates $P(s_i s_{\text{pivot}}^{-1})$, resp. for $Q$) are non-proportional, in the sense that some $2 \times 2$ minor $x_{i'}y_{j'} - x_{j'}y_{i'}$ is nonzero, then the chordal proximity $$\big|\mathrm{prox}_\mu(\text{evalVec } s\,P, \text{evalVec } s\,Q)\big| = \Big|\log \sup_i \mu(x_i) + \log \sup_j \mu(y_j) - \log \sup_{i,j} \mu(x_i y_j - x_j y_i)\Big|$$ is at most $4\big(\mathrm{linkBudget}(\Phi,s) + \mathrm{modulusExp}\big)\cdot\big(-\log \mu(p)\big)$.
--
--   This is one clause of the construction of a uniform multiplicative covering of $X_0(p)$ for $p \ge 5$: it bounds the chordal proximity between a place in the domain of the $\bar\infty$-chart, where the normalised good-family row is integral with a Hasse coordinate of absolute value one, and any rational place at which all Hasse members have absolute value less than one. It is used by [`ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom`](thm.html#ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom), which assembles the cross comparisons between chart domains and annuli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)

    (hint : ∀ i, goodFamily Φ i ∈ (infChart Γ).integers)
    (cQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → Fin r)
    (hrat : ∀ P ∈ (infChart Γ).dom, P.IsRational)
    (hratio : ∀ P ∈ (infChart Γ).dom, ∀ j, goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ (infChart Γ).integers)
    (hreg : ∀ P ∈ (infChart Γ).dom, ∀ j, goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (hhasse : ∀ P ∈ (infChart Γ).dom, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧
      μ (P.evalAt (goodFamily Φ l * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹)) = 1) :
    ∀ P ∈ (infChart Γ).dom, ∀ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      Q.IsRational →
      (∀ l : Fin r, 1 ≤ (l : ℕ) → goodFamily Φ l ∈ Q.toValuationSubring ∧ μ (Q.evalAt (goodFamily Φ l)) < 1) →
      (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
      |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
