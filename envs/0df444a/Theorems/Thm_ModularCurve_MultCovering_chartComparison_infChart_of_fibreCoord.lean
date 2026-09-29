-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_chartComparison_infChart_of_fibreCoord
-- name    : ModularCurve.MultCovering.chartComparison_infChart_of_fibreCoord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/ae682861-b340-5eeb-8e00-ebf2c28cf7fb
-- title:
--   Proximity comparison on the ∞̄ chart via a fibre coordinate
-- statement:
--   Fix a prime $p$ with $p \ge 5$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ belongs to $A.\text{nonunits}$, with residue field of characteristic $p$; fix a chart context $\Gamma$ for $p$ over $A$, an annulus context $\Delta$ over $\Gamma$, a natural number $r$, a family context $\Phi$ for $p$ and $r$, and a tuple $s : \mathrm{Fin}\ r \to \overline{\mathcal{F}}(1\cdot p)$ in the geometric modular function field of level $1\cdot p$ which is an embedding basis, i.e. linearly independent over $\overline{\mathbb{Q}}$ and spanning the Riemann–Roch space of the divisor $\mathrm{embDivisor}(1\cdot p)$. Let $T$ assign to each place of the level-one function field over the residue field of $A$ an element of $\overline{\mathcal{F}}(1\cdot p)$, and assume for every place $P$ in the domain of the chart $\mathrm{chart}\ \Gamma\ 0 = \mathrm{infChart}\ \Gamma$ that, writing $\bar P$ for the image of $P$ under the chart's place map, the element $T(\bar P) - T(\bar P)(P)$ (the value being taken by $P.\mathrm{evalAt}$ and pushed into the field) lies in the chart's ring of integers, its chart residue is nonzero and has order $1$ at $\bar P$, the order of $T(\bar P) - T(\bar P)(P)$ at $P$ is positive, and its order at every other place $Q$ of the chart domain with $\bar Q = \bar P$ is zero. Then for every nonarchimedean absolute value $\mu$ on $\overline{\mathbb{Q}}$ whose unit ball is exactly $A$, and all places $P \neq Q$ of the chart domain whose evaluation vectors $\mathrm{evalVec}\ s\ P$ and $\mathrm{evalVec}\ s\ Q$ (coordinates $V.\mathrm{evalAt}(s_i s_{\mathrm{pivot}}^{-1})$) are non-proportional, in the sense that some $2\times 2$ minor $\mathrm{evalVec}\ s\ P\ i' \cdot \mathrm{evalVec}\ s\ Q\ j' - \mathrm{evalVec}\ s\ P\ j' \cdot \mathrm{evalVec}\ s\ Q\ i'$ is nonzero: if $\bar P = \bar Q$ then $|\mathrm{prox}_\mu(\mathrm{evalVec}\ s\ P, \mathrm{evalVec}\ s\ Q) + \log \mu\bigl(T(\bar P)(P) - T(\bar P)(Q)\bigr)| \le \mathrm{compConst}\ \Phi\ s\ hs \cdot (-\log \mu(p))$, and if $\bar P \neq \bar Q$ then $|\mathrm{prox}_\mu(\mathrm{evalVec}\ s\ P, \mathrm{evalVec}\ s\ Q)| \le \mathrm{compConst}\ \Phi\ s\ hs \cdot (-\log \mu(p))$; here $\mathrm{prox}_\mu(x,y) = \log \sup_i \mu(x_i) + \log \sup_i \mu(y_i) - \log \sup_{i,j} \mu(x_i y_j - x_j y_i)$ and $\mathrm{compConst}\ \Phi\ s\ hs = 4(\mathrm{linkBudget}\ \Phi\ s\ hs + \mathrm{modulusExp})$.
--
--   This is the comparison clause, on the $\bar\infty$ chart of the prime-level covering of $X_0(p)$, between the chordal proximity of two points measured through an arbitrary embedding basis $s$ and the $\mu$-distance of their fibre coordinates: points with the same reduction are close up to the fibre coordinate, points with different reductions are at bounded proximity, both with one constant depending only on $\Phi$ and $s$. The fibre coordinate $T$ is abstracted as a binder so that the assembled statement [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le), which cites this result, may supply its own.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_chartComparison_infChart_of_fibreCoord.lean

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

theorem ModularCurve.MultCovering.chartComparison_infChart_of_fibreCoord (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (T : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → ↥(modularFunctionFieldBar (1 * p)))
    (hT : ∀ P ∈ (chart Γ 0).dom,
      ∃ h : T ((chart Γ 0).placeMap P) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (P.evalAt (T ((chart Γ 0).placeMap P)))
          ∈ (chart Γ 0).integers,
        (chart Γ 0).residue ⟨_, h⟩ ≠ 0 ∧ ((chart Γ 0).placeMap P).ord ((chart Γ 0).residue ⟨_, h⟩) = 1 ∧
        0 < P.ord (T ((chart Γ 0).placeMap P) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (P.evalAt (T ((chart Γ 0).placeMap P)))) ∧
        ∀ Q ∈ (chart Γ 0).dom, (chart Γ 0).placeMap Q = (chart Γ 0).placeMap P → Q ≠ P →
          Q.ord (T ((chart Γ 0).placeMap P) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (P.evalAt (T ((chart Γ 0).placeMap P)))) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ (chart Γ 0).dom, ∀ Q ∈ (chart Γ 0).dom, P ≠ Q →
        (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
        ((chart Γ 0).placeMap P = (chart Γ 0).placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (T ((chart Γ 0).placeMap P)) - Q.evalAt (T ((chart Γ 0).placeMap P))))|
            ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        ((chart Γ 0).placeMap P ≠ (chart Γ 0).placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ)))) := by sorry
