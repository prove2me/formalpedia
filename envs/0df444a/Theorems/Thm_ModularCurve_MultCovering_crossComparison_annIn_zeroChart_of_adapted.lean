-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_adapted
-- name    : ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_adapted
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/cfc9ecbb-b1f6-5857-bfd0-1b6f92413c35
-- title:
--   Chordal separation of supersingular tubes from the ̄0-chart
-- statement:
--   Fix a prime $p$ with $13 \le p$ and a family context $\Phi : \mathrm{FamCtx}\ p\ r$, consisting of $r$ elements $t_l$ of the geometric modular function field $\mathrm{modularFunctionFieldBar}(1\cdot p)$ together with rational expansions $t^{\mathbb Q}_l$ in $\mathrm{modularFunctionFieldFull}(1\cdot p)$, satisfying the embedding-basis, normalisation and chart-reduction axioms of that structure. Three hypotheses on $\Phi$ are assumed: (i) for every $c : \mathrm{Fin}\ r \to \mathbb Q$, all Laurent coefficients of $\sum_i c_i t^{\mathbb Q}_i$ are $p$-adically integral if and only if every $c_i$ is; (ii) likewise all coefficients of $\sum_i c_i \,\mathrm{frickeInvolutionFull}(1\cdot p)(t^{\mathbb Q}_i)$ are integral if and only if $\mathrm{padicValRat}\ p\ (c_i) \ge -\mathrm{hasseExp}\ \Phi\ i$ for all $i$; (iii) for every valuation subring $A$ of $\overline{\mathbb Q}$ in which $p$ is a non-unit, with residue characteristic $p$, and every chart context $\Gamma$ over $A$, the rescaled members $\mathrm{goodFamilyZero}\ \Phi\ l = p^{-\mathrm{hasseExp}\ \Phi\ l}\, t_l$ lie in the integers of $\mathrm{zeroChart}\ \Gamma$ and their residues are linearly independent over the residue field of $A$. Let $s$ be a family with $\mathrm{IsEmbBasis}(1\cdot p)\ s$, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of $\mathrm{embDivisor}(1\cdot p)$. Let $A$ be such a valuation subring, $\Gamma$ a chart context over $A$ and $\Delta$ an annulus context over $\Gamma$. The conclusion: for every non-archimedean real absolute value $\mu$ on $\overline{\mathbb Q}$ whose closed unit ball is exactly $A$, every index $e < \mathrm{mAnnuli}\ p$, every place $R$ in the domain of the annulus $\Delta.\mathrm{annIn}\ e$ and every place $Q$ in the domain of $\mathrm{zeroChart}\ \Gamma$ whose evaluation vectors are non-proportional (some $2\times2$ minor $\mathrm{evalVec}\ s\ R\ i' \cdot \mathrm{evalVec}\ s\ Q\ j' - \mathrm{evalVec}\ s\ R\ j' \cdot \mathrm{evalVec}\ s\ Q\ i'$ is non-zero), one has $|\mathrm{prox}_\mu(\mathrm{evalVec}\ s\ R, \mathrm{evalVec}\ s\ Q)| \le \mathrm{compConst}\ \Phi\ s\ hs \cdot (-\log \mu(p))$, where $\mathrm{prox}$ is $\log \sup_i \mu(x_i) + \log \sup_j \mu(y_j) - \log \sup_{i,j} \mu(x_i y_j - x_j y_i)$ and $\mathrm{compConst}\ \Phi\ s\ hs = 4(\mathrm{linkBudget}\ \Phi\ s\ hs + 3)$.
--
--   This is the uniform chordal-separation estimate between a supersingular annulus of the covering of $X_0(p)$ and the $\bar0$-chart, expressed in the coordinates of an embedding basis $s$ of the Riemann–Roch space attached to $\mathrm{embDivisor}(1\cdot p)$, with a bound depending only on $\Phi$ and $s$ through $\mathrm{compConst}$. It is used by [`ModularCurve.MultCovering.crossComparison_annIn_zeroChart`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_zeroChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_zeroChart_of_adapted.lean

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

theorem ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_adapted (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • Φ.toFamData.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (Φ.toFamData.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp Φ.toFamData i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hAd : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
        [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
        ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
          LinearIndependent (IsLocalRing.ResidueField ↥A)
            (fun l => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ e : Fin (mAnnuli p), ∀ R ∈ (Δ.annIn e).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (∃ i' j', evalVec s R i' * evalVec s Q j' ≠ evalVec s R j' * evalVec s Q i') →
        |prox μ (evalVec s R) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
