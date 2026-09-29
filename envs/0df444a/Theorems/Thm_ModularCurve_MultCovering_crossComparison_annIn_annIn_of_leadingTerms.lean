-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_leadingTerms
-- name    : ModularCurve.MultCovering.crossComparison_annIn_annIn_of_leadingTerms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/0a6ba7fb-6b99-5ea0-8f38-c2e944ff65db
-- title:
--   Cross-comparison of two wide tubes by leading terms
-- statement:
--   Let $p$ be a prime and $A$ a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ and with residue field of characteristic $p$. Let $\Gamma$ be chart data for level $1\cdot p$ over $A$ (giving the charts `infChart Γ`, `zeroChart Γ`, the supersingular $j$-values $\mathrm{ssValue}\,\Gamma\,e$ for $e$ among the $\mathrm{mAnnuli}\,p$ indices, and the node places $\mathrm{nodeTgt}\,\Gamma\,e$, $\mathrm{nodeSrc}\,\Gamma\,e$ at $j=\mathrm{ssValue}\,\Gamma\,e$ and $j=(\mathrm{ssValue}\,\Gamma\,e)^p$), and let $\Delta$ be annulus data over $\Gamma$, with tubes $\Delta.\mathrm{annIn}\,e$ and $\Delta.\mathrm{annOut}\,e$. Let $\Phi$ be a family context with $r$ members $t_l=\mathrm{goodFamily}\,\Phi\,l$, rescaled members $t'_l=p^{-\mathrm{hasseExp}\,\Phi\,l}\,t_l$, and let $s$ be an $r$-tuple in the base-changed modular function field of level $1\cdot p$ that is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of the embedding divisor. Assume: $e\ne e'$; all $t_l$ lie in the integers of `infChart Γ` and all $t'_l$ in those of `zeroChart Γ`; the parameters of $\Delta.\mathrm{annOut}\,e$ and $\Delta.\mathrm{annOut}\,e'$ lie in the integers of `infChart Γ`; indices $l_1,l_2,l_3\ge 1$ with $l_2\ne l_3$; the `infChart` residues of $t_{l_1},t_{l_2},t_{l_3}$ have order $1$ at $\mathrm{nodeTgt}\,\Gamma\,e$ and at $\mathrm{nodeTgt}\,\Gamma\,e'$; the `zeroChart` residue of $t'_{l_1}$ has order $0$ at $\mathrm{nodeSrc}\,\Gamma\,e$ and at $\mathrm{nodeSrc}\,\Gamma\,e'$, with distinct values there; the `zeroChart` residues of $t'_{l_2}$ and $t'_{l_3}$ have order $\le 0$ at $\mathrm{nodeSrc}\,\Gamma\,e$; $\mathrm{hasseExp}\,\Phi\,l_1<\mathrm{hasseExp}\,\Phi\,l_2$ and $<\mathrm{hasseExp}\,\Phi\,l_3$; every place in the domain of $\Delta.\mathrm{annIn}\,e'$ has order $0$ at $t_{l_2}$ and at $t_{l_3}$; and, writing $w_{l,\varepsilon}$ for the value at $\mathrm{nodeTgt}\,\Gamma\,\varepsilon$ of the `infChart` residue of $t_l$ divided by that of the parameter of $\Delta.\mathrm{annOut}\,\varepsilon$, one has $w_{l_2,e}w_{l_3,e'}\ne w_{l_3,e}w_{l_2,e'}$. Then for every non-archimedean absolute value $\mu$ on $\overline{\mathbb Q}$ whose closed unit ball is exactly $A$, and all places $R$ in the domain of $\Delta.\mathrm{annIn}\,e$ and $R'$ in that of $\Delta.\mathrm{annIn}\,e'$ such that the value of $R$ at the parameter of $\Delta.\mathrm{annOut}\,e$ lies in $p^{\mathrm{hasseExp}\,\Phi\,l_1}A$ or the value of $R'$ at the parameter of $\Delta.\mathrm{annOut}\,e'$ lies in $p^{\mathrm{hasseExp}\,\Phi\,l_1}A$, if the vectors $\mathrm{evalVec}\,s\,R$ and $\mathrm{evalVec}\,s\,R'$ have some non-vanishing $2\times 2$ minor, then $|\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,R,\mathrm{evalVec}\,s\,R')|\le \mathrm{compConst}\,\Phi\,s\,hs\cdot(-\log\mu(p))$, the constant being $4$ times the link budget of $(\Phi,s)$ plus $3$.
--
--   This is the tube-against-tube case of the cross-piece proximity estimate for the supersingular annuli of the covering of $X_0(p)$: the chordal distance between two points lying on distinct wide tubes, below the first zero level $p^{n_{l_1}}$, is bounded in terms of $-\log\mu(p)$ with the universal constant $\mathrm{compConst}$. It is used by [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent), where the leading-term hypotheses on the members $t_{l_1},t_{l_2},t_{l_3}$ are replaced by orthogonality and linear-independence conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_leadingTerms.lean

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

open IsLocalRing ModularCurve ModularCurve.MultCovering
open AlgebraicCurve

theorem ModularCurve.MultCovering.crossComparison_annIn_annIn_of_leadingTerms (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') (l₁ l₂ l₃ : Fin r) (hl₁ : 1 ≤ (l₁ : ℕ)) (hl₂ : 1 ≤ (l₂ : ℕ)) (hl₃ : 1 ≤ (l₃ : ℕ))
    (hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers)
    (hint0 : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut e).param ∈ (infChart Γ).integers) (hz' : (Δ.annOut e').param ∈ (infChart Γ).integers)

    (hord₁ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint l₁⟩) = 1)
    (hord₁' : (nodeTgt Γ e').ord ((infChart Γ).residue ⟨goodFamily Φ l₁, hint l₁⟩) = 1)
    (hβ₁ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩) = 0)
    (hβ₁' : (nodeSrc Γ e').ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩) = 0)
    (hsep₁ : (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩)
        ≠ (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₁, hint0 l₁⟩))

    (h23 : l₂ ≠ l₃)
    (hord₂ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₂, hint l₂⟩) = 1)
    (hord₂' : (nodeTgt Γ e').ord ((infChart Γ).residue ⟨goodFamily Φ l₂, hint l₂⟩) = 1)
    (hord₃ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hint l₃⟩) = 1)
    (hord₃' : (nodeTgt Γ e').ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hint l₃⟩) = 1)
    (hβ₂ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₂, hint0 l₂⟩) ≤ 0)
    (hβ₃ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₃, hint0 l₃⟩) ≤ 0)
    (hn₂ : hasseExp Φ.toFamData l₁ < hasseExp Φ.toFamData l₂) (hn₃ : hasseExp Φ.toFamData l₁ < hasseExp Φ.toFamData l₃)
    (hzf₂' : ∀ R' ∈ (Δ.annIn e').dom, R'.ord (goodFamily Φ l₂) = 0)
    (hzf₃' : ∀ R' ∈ (Δ.annIn e').dom, R'.ord (goodFamily Φ l₃) = 0)
    (hdet : (nodeTgt Γ e).evalAt ((infChart Γ).residue ⟨goodFamily Φ l₂, hint l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e).param, hz⟩)⁻¹)
          * (nodeTgt Γ e').evalAt ((infChart Γ).residue ⟨goodFamily Φ l₃, hint l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e').param, hz'⟩)⁻¹)
        ≠ (nodeTgt Γ e).evalAt ((infChart Γ).residue ⟨goodFamily Φ l₃, hint l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e).param, hz⟩)⁻¹)
          * (nodeTgt Γ e').evalAt ((infChart Γ).residue ⟨goodFamily Φ l₂, hint l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e').param, hz'⟩)⁻¹)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        ((∃ m : AlgebraicClosure ℚ, m ∈ A ∧
            R.evalAt (Δ.annOut e).param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₁ * m) ∨
         (∃ m : AlgebraicClosure ℚ, m ∈ A ∧
            R'.evalAt (Δ.annOut e').param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₁ * m)) →
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
