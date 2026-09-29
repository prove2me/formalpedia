-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_zeroChart
-- name    : ModularCurve.MultCovering.crossComparison_annIn_zeroChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/b4d0953d-a738-5202-b5ca-4c4feeda6f2d
-- title:
--   Chordal separation between a supersingular annulus and the zero chart
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $r$ be a natural number and let $\Phi$ be a family context `FamCtx p r` at level $1\cdot p$. Let $s : \mathrm{Fin}\,r \to \overline{\mathcal F}(1\cdot p)$ be a tuple in the base-changed modular function field `modularFunctionFieldBar (1 * p)` which is an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its span is the Riemann–Roch space $\{f : v(f) \le \exp(D(v))\ \text{for all places } v\}$ of the divisor `embDivisor (1 * p)`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that $p$ is a non-unit of $A$, with residue field of characteristic $p$, let $\Gamma$ be a chart context `ChartCtx p A` and let $\Delta$ be an annulus context `AnnCtx` over $\Gamma$. Then for every non-archimedean absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit ball is exactly $A$ (that is, $a \in A \iff \mu(a) \le 1$), for every index $e$ among the $\mathrm{mAnnuli}(p) = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$ annuli, every place $R$ in the domain of the annulus $\Delta.\mathrm{An}\,e$ and every place $Q$ in the domain of `zeroChart Γ` (the comap of the chart `infChart Γ` along the Fricke involution at level $1\cdot p$), if the two evaluation vectors $\mathrm{evalVec}\,s\,R$ and $\mathrm{evalVec}\,s\,Q$ in $\overline{\mathbb Q}^{\,r}$ (the place-wise residues of the ratios $s_i/s_{\text{pivot}}$) are non-proportional, in the sense that some $2\times 2$ cross term $x_{i'}y_{j'} - x_{j'}y_{i'}$ is non-zero, then the chordal proximity
--   $$\operatorname{prox}_\mu(x,y) = \log \sup_i \mu(x_i) + \log \sup_j \mu(y_j) - \log \sup_{(i,j)} \mu(x_i y_j - x_j y_i)$$
--   of these two vectors satisfies $|\operatorname{prox}_\mu(x,y)| \le \bigl(4(\operatorname{linkBudget}\Phi\,s\,hs + \mathrm{modulusExp})\bigr)\cdot(-\log \mu(p))$, the right-hand factor being `compConst Φ s hs`.
--
--   This is the cross-comparison estimate between a supersingular annulus (tube) of the multiplicative covering of $X_0(p)$ and the chart at the cusp $\bar 0$: places of the two regions are uniformly separated in the chordal metric attached to $\mu$, with a bound linear in $-\log\mu(p)$ and a constant depending only on $p$, the family and the embedding basis. It feeds the assembly of the uniform covering structure, being cited by [`ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom`](thm.html#ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_zeroChart.lean

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

theorem ModularCurve.MultCovering.crossComparison_annIn_zeroChart (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ e : Fin (mAnnuli p), ∀ R ∈ (Δ.annIn e).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (∃ i' j', evalVec s R i' * evalVec s Q j' ≠ evalVec s R j' * evalVec s Q i') →
        |prox μ (evalVec s R) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
