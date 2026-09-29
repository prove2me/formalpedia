-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_chartComparison_zeroChart_of_chartData_of_fibreCoord
-- name    : ModularCurve.MultCovering.chartComparison_zeroChart_of_chartData_of_fibreCoord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/d802feb0-c88a-5e84-a77b-42772ba8b3ff
-- title:
--   Chordal proximity comparison on the ̄ 0 chart of X₀(p)
-- statement:
--   Fix a prime $p$ with $5 \le p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, whose residue field has characteristic $p$; let $\Gamma$ be a chart context `ChartCtx p A`, $\Delta$ an annulus context `AnnCtx Γ`, and $\Phi$ a certified family context `FamCtx p r` (a family $t_0,\dots,t_{r-1}$ in the level-$p$ field with $t_0 = 1$, forming an embedding basis and with prescribed reductions on both charts). Let $s : \mathrm{Fin}\,r \to \overline{\mathcal F}(p)$ satisfy `IsEmbBasis`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of `embDivisor (1 * p)`. Write $C =$ `chart Γ 1`, the zero chart, and $u_l = p^{-\mathrm{hasseExp}_l} t_l$ for `goodFamilyZero`. The hypotheses are the chart data of the family $u$ on $C$: each $u_l$ lies in the valuation subring $C$.integers; index maps $c_Q, i_Q$ from places of the reduced curve over the residue field of $A$ to $\mathrm{Fin}\,r$; every place $P$ in $C$.dom and its reduction $\bar P = C.\mathrm{placeMap}\,P$ are rational; the chart residue of $u_{c_Q(\bar P)}$ is nonzero; all ratios $u_j u_{c_Q(\bar P)}^{-1}$ lie in $C$.integers and in the valuation ring of $P$; the residue of $u_{i_Q(\bar P)} u_{c_Q(\bar P)}^{-1}$ minus its value at $\bar P$ has order exactly $1$ at $\bar P$; and for places $P, Q$ of $C$.dom with $\bar P \ne \bar Q$ some $2\times 2$ minor of the matrix of values of the reduced ratios at $\bar P$ and $\bar Q$ is nonzero. Finally $T$ assigns to each place of the reduced curve a function such that, for $P \in C$.dom, $T(\bar P)$ minus its value at $P$ lies in $C$.integers, has nonzero chart residue of order $1$ at $\bar P$, has positive order at $P$, and has order $0$ at every other place of $C$.dom with the same reduction as $P$. The conclusion: for every non-archimedean absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit ball is exactly $A$, and all $P \ne Q$ in $C$.dom whose evaluation vectors `evalVec s P`, `evalVec s Q` are non-proportional (some $2 \times 2$ minor is nonzero), one has $\bigl|\mathrm{prox}_\mu(s(P), s(Q)) + \log \mu\bigl(P.\mathrm{evalAt}\,T(\bar P) - Q.\mathrm{evalAt}\,T(\bar P)\bigr)\bigr| \le 4(\mathrm{linkBudget} + 3)\cdot(-\log \mu(p))$ when $\bar P = \bar Q$, and $|\mathrm{prox}_\mu(s(P), s(Q))| \le 4(\mathrm{linkBudget} + 3)\cdot(-\log \mu(p))$ when $\bar P \ne \bar Q$, where $\mathrm{prox}_\mu(x,y) = \log \sup_i \mu(x_i) + \log \sup_i \mu(y_i) - \log \sup_{i,j} \mu(x_i y_j - x_j y_i)$ and the constant is `compConst Φ s hs`.
--
--   This is the chart-comparison estimate on the zero chart of the multiplicative covering of $X_0(p)$: it compares the chordal proximity of two $\overline{\mathbb Q}$-points of the embedded curve, measured through an embedding basis $s$ of the Riemann–Roch space of the embedding divisor, with the $\mu$-distance of their fibre coordinates, the discrepancy being bounded by an explicit multiple of $-\log\mu(p)$ that is uniform in $A$ and $\mu$. The chart data of the rescaled family $p^{-n_l}t_l$ and the fibre coordinate $T$ are carried as hypotheses; the result is used in the construction of the uniform multiplicative covering with certified family at primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_chartComparison_zeroChart_of_chartData_of_fibreCoord.lean

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

theorem ModularCurve.MultCovering.chartComparison_zeroChart_of_chartData_of_fibreCoord (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (hint0 : ∀ i, goodFamilyZero Φ.toFamData i ∈ (chart Γ 1).integers)
    (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → Fin r)
    (hrat : ∀ P ∈ (chart Γ 1).dom, P.IsRational ∧ ((chart Γ 1).placeMap P).IsRational)
    (hcQ : ∀ P ∈ (chart Γ 1).dom, (chart Γ 1).residue ⟨goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)), hint0 _⟩ ≠ 0)
    (hratio : ∀ P ∈ (chart Γ 1).dom, ∀ j, goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)))⁻¹ ∈ (chart Γ 1).integers)
    (hreg : ∀ P ∈ (chart Γ 1).dom, ∀ j, goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (himm : ∀ P ∈ (chart Γ 1).dom, ∀ hmem : goodFamilyZero Φ.toFamData (iQ ((chart Γ 1).placeMap P)) * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)))⁻¹ ∈ (chart Γ 1).integers,
      ((chart Γ 1).placeMap P).ord ((chart Γ 1).residue ⟨_, hmem⟩
        - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (((chart Γ 1).placeMap P).evalAt ((chart Γ 1).residue ⟨_, hmem⟩))) = 1)
    (hsep : ∀ P ∈ (chart Γ 1).dom, ∀ Q ∈ (chart Γ 1).dom, (chart Γ 1).placeMap P ≠ (chart Γ 1).placeMap Q →
      ∀ (hmP : ∀ j, goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap P)))⁻¹ ∈ (chart Γ 1).integers)
        (hmQ : ∀ j, goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((chart Γ 1).placeMap Q)))⁻¹ ∈ (chart Γ 1).integers),
      ∃ i j, ((chart Γ 1).placeMap P).evalAt ((chart Γ 1).residue ⟨_, hmP i⟩) * ((chart Γ 1).placeMap Q).evalAt ((chart Γ 1).residue ⟨_, hmQ j⟩)
        ≠ ((chart Γ 1).placeMap P).evalAt ((chart Γ 1).residue ⟨_, hmP j⟩) * ((chart Γ 1).placeMap Q).evalAt ((chart Γ 1).residue ⟨_, hmQ i⟩))
    (T : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → ↥(modularFunctionFieldBar (1 * p)))
    (hT : ∀ P ∈ (chart Γ 1).dom,
      ∃ h : T ((chart Γ 1).placeMap P) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (P.evalAt (T ((chart Γ 1).placeMap P)))
          ∈ (chart Γ 1).integers,
        (chart Γ 1).residue ⟨_, h⟩ ≠ 0 ∧ ((chart Γ 1).placeMap P).ord ((chart Γ 1).residue ⟨_, h⟩) = 1 ∧
        0 < P.ord (T ((chart Γ 1).placeMap P) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (P.evalAt (T ((chart Γ 1).placeMap P)))) ∧
        ∀ Q ∈ (chart Γ 1).dom, (chart Γ 1).placeMap Q = (chart Γ 1).placeMap P → Q ≠ P →
          Q.ord (T ((chart Γ 1).placeMap P) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (P.evalAt (T ((chart Γ 1).placeMap P)))) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ (chart Γ 1).dom, ∀ Q ∈ (chart Γ 1).dom, P ≠ Q →
        (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
        ((chart Γ 1).placeMap P = (chart Γ 1).placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (T ((chart Γ 1).placeMap P)) - Q.evalAt (T ((chart Γ 1).placeMap P))))|
            ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        ((chart Γ 1).placeMap P ≠ (chart Γ 1).placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ)))) := by sorry
