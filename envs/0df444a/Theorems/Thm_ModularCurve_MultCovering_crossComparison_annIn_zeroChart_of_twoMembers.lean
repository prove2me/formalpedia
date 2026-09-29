-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers
-- name    : ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_twoMembers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/26929fb7-26d4-587e-b2bc-6c5d91a0bea6
-- title:
--   Chordal separation of a supersingular annulus from the ̄0-chart
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb Q}$ for which $p$ is a non-unit of $A$ and whose residue field has characteristic $p$, a chart context $\Gamma$ for $p$ and $A$ (supplying the $\bar\infty$-chart `infChart Γ`, its Fricke-conjugate $\bar0$-chart `zeroChart Γ`, the supersingular values $a_e=$ `ssValue Γ e`, and the node places `nodeTgt Γ e`, `nodeSrc Γ e` of $a_e$ and $a_e^p$ on the two lines), and an annulus context $\Delta$ over $\Gamma$. Let $\Phi$ be a family context of rank $r$ with members $t_l=$ `goodFamily Φ l` and rescalings $t'_l=p^{-n_l}t_l$, $n_l=$ `hasseExp Φ.toFamData l`, and let $s\colon \mathrm{Fin}\,r\to \overline{\mathbb Q}$-points of the level-$p$ modular function field be an embedding basis, i.e. linearly independent over $\overline{\mathbb Q}$ with span the Riemann–Roch space of `embDivisor (1*p)`. Fix an index $e$ and two members $l_1,l_2\ge 1$ such that $t_{l_1},t_{l_2}$ lie in the integers of the $\bar\infty$-chart with residues of order $1$ at `nodeTgt Γ e`, such that $t'_{l_1},t'_{l_2}$ lie in the integers of the $\bar0$-chart with residues of order $0$, resp. order $\le 0$, at `nodeSrc Γ e`, such that $n_{l_1}<n_{l_2}$, and such that for every place $Q$ in the domain of the $\bar0$-chart the value of the residue of $t'_{l_1}$ at `(zeroChart Γ).placeMap Q` differs from its value at `nodeSrc Γ e`. Then for every non-archimedean real absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit ball is exactly $A$, every place $R$ in the domain of the annulus `Δ.annIn e`, and every place $Q$ in the domain of the $\bar0$-chart whose evaluation vectors `evalVec s R` and `evalVec s Q` are not proportional (some $2\times2$ minor is non-zero), the chordal proximity satisfies $|\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,R,\mathrm{evalVec}\,s\,Q)|\le 4\big(\mathrm{linkBudget}\,\Phi\,s\,hs+3\big)\cdot(-\log\mu(p))$.
--
--   This is the cross-piece estimate between a supersingular tube and the $\bar0$-component chart in the multiplicative-covering analysis of $X_0(p)$ over a valuation ring above $p$, valid at a node of any width once two members of the good family provide the stated order and separation certificate. It is used by [`ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_adapted`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_adapted).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_twoMembers.lean

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

theorem ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_twoMembers (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (e : Fin (mAnnuli p)) (l₁ l₂ : Fin r) (hl₁ : 1 ≤ (l₁ : ℕ)) (hl₂ : 1 ≤ (l₂ : ℕ))
    (hint₁ : goodFamily Φ l₁ ∈ (infChart Γ).integers)
    (hord₁ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint₁⟩) = 1)
    (hint₂ : goodFamily Φ l₂ ∈ (infChart Γ).integers)
    (hord₂ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₂, hint₂⟩) = 1)
    (hint0₁ : goodFamilyZero Φ.toFamData l₁ ∈ (zeroChart Γ).integers)
    (hβ₁ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0₁⟩) = 0)
    (hint0₂ : goodFamilyZero Φ.toFamData l₂ ∈ (zeroChart Γ).integers)
    (hβ₂ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₂, hint0₂⟩) ≤ 0)
    (hn : hasseExp Φ.toFamData l₁ < hasseExp Φ.toFamData l₂)
    (hsep : ∀ Q ∈ (zeroChart Γ).dom,
      ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0₁⟩)
        ≠ (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0₁⟩)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (∃ i' j', evalVec s R i' * evalVec s Q j' ≠ evalVec s R j' * evalVec s Q i') →
        |prox μ (evalVec s R) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
