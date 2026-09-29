-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn
-- name    : ModularCurve.MultCovering.crossComparison_annIn_annIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/5db2c529-666f-52c2-b33f-2614f3ece717
-- title:
--   Chordal separation across two distinct supersingular annuli
-- statement:
--   Fix a prime $p$ with $5 \le p$, a natural number $r$, and a family context $\Phi : \mathrm{FamCtx}\,p\,r$ (a `FamData` for $p$ and $r$ whose function system $t$ is an embedding basis, is normalised by $t_l = 1$ at the index $l = 0$, and satisfies the prescribed integrality and residue conditions at the infinity and zero charts over every valuation subring lying over $p$). Let $s : \mathrm{Fin}\,r \to \overline{\mathcal F}(1\cdot p)$ be a system of elements of the base-changed modular function field of level $1 \cdot p$ satisfying `IsEmbBasis`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its span is the Riemann–Roch space of the embedding divisor of that level. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ in its nonunits (`LiesOverPrime`) and residue field of characteristic $p$, let $\Gamma$ be a chart context for $p$ and $A$, let $\Delta$ be an annulus context over $\Gamma$, and let $e \ne e'$ be indices in $\mathrm{Fin}(\mathrm{mAnnuli}\,p)$, where $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$. Then for every real-valued absolute value $\mu$ on $\overline{\mathbb Q}$ that is nonarchimedean and satisfies $A = \{a : \mu(a) \le 1\}$, for every place $R$ in the domain of the inner annulus $\Delta.\mathrm{An}\,e$ and every place $R'$ in the domain of $\Delta.\mathrm{An}\,e'$ whose evaluation vectors are non-proportional (there are indices $i', j'$ with $\mathrm{evalVec}\,s\,R\,i' \cdot \mathrm{evalVec}\,s\,R'\,j' \ne \mathrm{evalVec}\,s\,R\,j' \cdot \mathrm{evalVec}\,s\,R'\,i'$), one has $$\bigl|\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,R, \mathrm{evalVec}\,s\,R')\bigr| \le \mathrm{compConst}(\Phi, s) \cdot \bigl(-\log \mu(p)\bigr),$$ where $\mathrm{evalVec}\,s\,R\,i$ is the residue at $R$ of $s_i$ divided by the pivot coordinate, $\mathrm{prox}_\mu(x,y) = \log \sup_i \mu(x_i) + \log \sup_j \mu(y_j) - \log \sup_{i,j} \mu(x_i y_j - x_j y_i)$, and $\mathrm{compConst}(\Phi,s) = 4\bigl(\mathrm{linkBudget}(\Phi,s) + \mathrm{modulusExp}\bigr)$.
--
--   This is the cross-annulus case of the chordal comparison estimate for the prime-level covering of $X_0(p)$: points lying on two different supersingular annuli of the chart-and-annulus decomposition have chordal proximity bounded uniformly, with a bound linear in $-\log\mu(p)$ and a constant depending only on the family and the embedding basis. It feeds into [`ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom`](thm.html#ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom), which assembles the chart and annulus cases into a single comparison statement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.MultCovering

theorem ModularCurve.MultCovering.crossComparison_annIn_annIn (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
