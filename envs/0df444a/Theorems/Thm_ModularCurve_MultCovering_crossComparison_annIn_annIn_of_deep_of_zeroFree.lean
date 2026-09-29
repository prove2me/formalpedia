-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_deep_of_zeroFree
-- name    : ModularCurve.MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/3294a3b9-316e-55c4-bcae-2c2d0f52d099
-- title:
--   Chordal proximity bound across two distinct supersingular annuli
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$, in the sense that $p$ is a non-unit of $A$, with residue field of characteristic $p$. Let $\Gamma$ be a chart context for $p$ and $A$, $\Delta$ an annulus context over $\Gamma$, $\Phi$ a good-family context of rank $r$ for $p$, and $s : \mathrm{Fin}\,r \to \overline{\mathbb Q}\text{-points of } \mathtt{modularFunctionFieldBar}(1\cdot p)$ an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of the divisor $\mathtt{embDivisor}(1\cdot p)$. Let $e \neq e'$ be two of the $\mathtt{mAnnuli}\,p$ edges and let $l_1$ be an index with $1 \le l_1$ such that: the member $t_{l_1} = \mathtt{goodFamily}\,\Phi\,l_1$ lies in the integers of the chart $\mathtt{infChart}\,\Gamma$ and its residue has order exactly $1$ at both nodes $\mathtt{nodeTgt}\,\Gamma\,e$ and $\mathtt{nodeTgt}\,\Gamma\,e'$ (the geometric places of the level-one function field at $\mathtt{ssValue}\,\Gamma\,e$ and $\mathtt{ssValue}\,\Gamma\,e'$); the rescaled member $\mathtt{goodFamilyZero}\,\Phi\,l_1 = p^{-n_{l_1}} t_{l_1}$, with $n_{l_1} = \mathtt{hasseExp}\,\Phi\,l_1$, lies in the integers of $\mathtt{zeroChart}\,\Gamma$ and its residue has order $0$ at $\mathtt{nodeSrc}\,\Gamma\,e$ (the place at $(\mathtt{ssValue}\,\Gamma\,e)^p$); and $t_{l_1}$ has order $0$ at every place in the domain of the annulus $\Delta.\mathtt{annIn}\,e'$. Then for every non-archimedean absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit ball is exactly $A$ (i.e. $a \in A \iff \mu(a) \le 1$), every place $R$ in the domain of $\Delta.\mathtt{annIn}\,e$ and every place $R'$ in the domain of $\Delta.\mathtt{annIn}\,e'$, if the value of the complementary parameter $(\Delta.\mathtt{annOut}\,e).\mathtt{param}$ at $R$ equals $p^{n_{l_1}}$ times an element of $A$, and if the evaluation vectors $\mathtt{evalVec}\,s\,R$ and $\mathtt{evalVec}\,s\,R'$ (the pivot-normalised coordinate vectors of $R$ and $R'$ in the basis $s$) are not proportional, in the sense that some $2 \times 2$ minor $x_{i'} y_{j'} - x_{j'} y_{i'}$ is non-zero, then $$\bigl|\mathtt{prox}\,\mu\,(\mathtt{evalVec}\,s\,R)\,(\mathtt{evalVec}\,s\,R')\bigr| \le \mathtt{compConst}\,\Phi\,s\,hs \cdot \bigl(-\log \mu(p)\bigr),$$ where the proximity is $\log \sup_i \mu(x_i) + \log \sup_i \mu(y_i) - \log \sup_{i,j} \mu(x_i y_j - x_j y_i)$ and the comparison constant is $4(\mathtt{linkBudget}\,\Phi\,s\,hs + 3)$.
--
--   This is one of the cross-annulus estimates in the archimedean-free geometry of the supersingular tubes of the prime-level covering of $X_0(p)$: it bounds the chordal proximity of two points lying on different tubes by a constant multiple of $-\log\mu(p)$, uniformly in the embedding basis used to coordinatise. It is the case in which a good-family member has a simple zero of its reduction at both nodes, order zero at the source node of $e$ and no zero at all on the tube of $e'$; it is invoked by [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_eq_eleven`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_eq_eleven) and by [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_deep_of_zeroFree.lean

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

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') (l₁ : Fin r) (hl₁ : 1 ≤ (l₁ : ℕ))
    (hint₁ : goodFamily Φ l₁ ∈ (infChart Γ).integers)
    (hord₁ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint₁⟩) = 1)
    (hord₁' : (nodeTgt Γ e').ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint₁⟩) = 1)
    (hint0₁ : goodFamilyZero Φ.toFamData l₁ ∈ (zeroChart Γ).integers)
    (hβ₁ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0₁⟩) = 0)
    (hzf₁' : ∀ R' ∈ (Δ.annIn e').dom, R'.ord (goodFamily Φ l₁) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∃ m : AlgebraicClosure ℚ, m ∈ A ∧
          R.evalAt (Δ.annOut e).param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₁ * m) →
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
