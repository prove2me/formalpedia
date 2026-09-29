-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one
-- name    : ModularCurve.MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/86a66b2e-48f9-5684-93ee-2b1d6866919e
-- title:
--   Tube-against-tube proximity bound at width-one supersingular nodes
-- statement:
--   Fix a prime $p$ with $5 \le p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$, in the sense that $p$ is a non-unit of $A$, whose residue field has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, $\Delta$ an annulus context `AnnCtx` over $\Gamma$, and $\Phi$ a family context `FamCtx p r` for some $r$. Let $s : \mathrm{Fin}\,r \to \overline{\mathbb Q}$-points of the function field `modularFunctionFieldBar (1 * p)` be an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of the divisor `embDivisor (1 * p)`. Let $e \ne e'$ be two of the `mAnnuli p` indices, and assume $\mathrm{jWidth}$ of the supersingular values $\mathrm{ssValue}\,\Gamma\,e$ and $\mathrm{ssValue}\,\Gamma\,e'$ both equal $1$, i.e. neither value is $0$ or $1728$. The conclusion: for every nonarchimedean real absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit ball is exactly $A$, for every place $R$ in the domain of the tube $\Delta.\mathrm{annIn}\,e$ (the places centred supersingularly at $\mathrm{ssValue}\,\Gamma\,e$ in the sense of `IsSSCentred`) and every $R'$ in the domain of $\Delta.\mathrm{annIn}\,e'$, if the evaluation vectors $\mathrm{evalVec}\,s\,R$ and $\mathrm{evalVec}\,s\,R'$ are non-proportional, witnessed by indices $i',j'$ with $\mathrm{evalVec}\,s\,R\,i' \cdot \mathrm{evalVec}\,s\,R'\,j' \ne \mathrm{evalVec}\,s\,R\,j' \cdot \mathrm{evalVec}\,s\,R'\,i'$, then $|\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,R, \mathrm{evalVec}\,s\,R')| \le \mathrm{compConst}\,\Phi\,s\,hs \cdot (-\log \mu(p))$, where $\mathrm{prox}_\mu(x,y) = \log \sup_i \mu(x_i) + \log \sup_j \mu(y_j) - \log \sup_{(i,j)} \mu(x_i y_j - x_j y_i)$ and $\mathrm{compConst}\,\Phi\,s\,hs = 4(\mathrm{linkBudget}\,\Phi\,s\,hs + \mathrm{modulusExp})$.
--
--   This is the tube-against-tube case, at supersingular nodes of width one, of the cross-comparison clause used in building a uniform multiplicative covering structure for the prime-level covering of $X_0(p)$: places lying in two distinct supersingular tubes are chordally far apart, with a bound linear in $-\log\mu(p)$ and a constant depending only on the family and the embedding basis. It is cited by [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent), which removes the width-one restriction on the two nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.lean

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

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e')
    (hwe : jWidth (ssValue Γ e) = 1) (hwe' : jWidth (ssValue Γ e') = 1) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
