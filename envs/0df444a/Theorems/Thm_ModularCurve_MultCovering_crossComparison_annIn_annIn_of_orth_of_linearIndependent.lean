-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_orth_of_linearIndependent
-- name    : ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/8e60b92c-44bf-56bb-9320-22e4c2168a53
-- title:
--   Tube-to-tube chordal comparison for adapted good families
-- statement:
--   Let $p \ge 13$ be a prime, $r$ a natural number, and $\Phi$ a family context of level $1\cdot p$ with $r$ members, so that in particular its members $t_l \in \overline{\mathcal F}(1\cdot p)$ form an embedding basis and come from rational Laurent expansions $\mathrm{tRat}_l$. Assume two $p$-adic orthogonality hypotheses for rational coefficient vectors $c : \mathrm{Fin}\,r \to \mathbb{Q}$: all Laurent coefficients of $\sum_i c_i\,\mathrm{tRat}_i$ have non-negative $p$-adic valuation precisely when every $c_i$ does, and all Laurent coefficients of $\sum_i c_i\,\sigma(\mathrm{tRat}_i)$, where $\sigma$ is the Fricke involution of the full modular function field of level $1\cdot p$, have non-negative valuation precisely when $-\mathrm{hasseExp}\,\Phi\,i \le v_p(c_i)$ for every $i$. Assume further that for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ and every chart context $\Gamma$ for $p$ over $A$, the rescaled members $p^{-\mathrm{hasseExp}\,\Phi\,l}\,t_l$ lie in the integers of the zero chart of $\Gamma$ and have residues linearly independent over the residue field of $A$. Let $s : \mathrm{Fin}\,r \to \overline{\mathcal F}(1\cdot p)$ be any embedding basis, that is, linearly independent over $\overline{\mathbb{Q}}$ and spanning the Riemann–Roch space of the cuspidal divisor $\mathrm{embDivisor}(1\cdot p)$. Fix such an $A$ with $p$ a non-unit, a chart context $\Gamma$ for $p$ over $A$, an annulus context $\Delta$ over $\Gamma$, and two distinct indices $e \ne e'$ in $\mathrm{Fin}(\mathrm{mAnnuli}\,p)$, where $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$. Then for every real absolute value $\mu$ on $\overline{\mathbb{Q}}$ that is non-archimedean and whose closed unit ball is exactly $A$, for every place $R$ in the domain of the annulus $\Delta.\mathrm{annIn}\,e$ and every place $R'$ in the domain of $\Delta.\mathrm{annIn}\,e'$ such that the evaluation vectors $\mathrm{evalVec}\,s\,R$ and $\mathrm{evalVec}\,s\,R'$ are non-proportional (some $2 \times 2$ minor $x_{i'}y_{j'} - x_{j'}y_{i'}$ is non-zero), the chordal proximity satisfies $|\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,R, \mathrm{evalVec}\,s\,R')| \le \mathrm{compConst}\,\Phi\,s\,hs \cdot (-\log \mu(p))$, where $\mathrm{prox}_\mu(x,y) = \log \sup_i \mu(x_i) + \log \sup_j \mu(y_j) - \log \sup_{i,j} \mu(x_iy_j - x_jy_i)$ and $\mathrm{compConst}\,\Phi\,s\,hs = 4(\mathrm{linkBudget}\,\Phi\,s\,hs + 3)$.
--
--   This is the case of the covering comparison in which the two places lie on two distinct supersingular annuli (tubes) of the semistable model of $X_0(p)$, and it is stated for a family context satisfying the orthogonality and zero-chart independence conditions of an adapted good family. It is used by [`ModularCurve.MultCovering.crossComparison_annIn_annIn`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn), which removes those conditions on the family by recombination and the family-independence of the comparison constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_orth_of_linearIndependent.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.MultCovering

theorem ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent (p : ℕ) [Fact p.Prime]
    (hp13 : 13 ≤ p) {r : ℕ} (Φ : FamCtx p r)
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
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
