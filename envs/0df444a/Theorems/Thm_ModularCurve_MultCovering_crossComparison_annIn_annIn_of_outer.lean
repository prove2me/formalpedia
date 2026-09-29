-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_outer
-- name    : ModularCurve.MultCovering.crossComparison_annIn_annIn_of_outer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/cac58a08-a4d3-5673-8193-b86334478e79
-- title:
--   Chordal cross-comparison of places in two distinct annuli
-- statement:
--   Fix a prime $p$ with $5 \le p$ and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$, in the sense that $p$ is a non-unit of $A$, and whose residue field has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A` and $\Delta$ an annulus context `AnnCtx` over $\Gamma$, so that for each edge $e$ among the $\mathrm{mAnnuli}(p) = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$ supersingular indices one has two annuli `Δ.annIn e` $=$ `Δ.An e` and `Δ.annOut e` $=$ `Δ.An' e` with a common domain of places, equal moduli, and parameters whose product is the modulus. Let $\Phi$ be a family context `FamCtx p r` with members $t_l =$ `goodFamily Φ l`, and let $s : \mathrm{Fin}\,r \to \overline{\mathbb Q}\text{-rational functions of level } 1\cdot p$ be an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and spans the Riemann–Roch space of the embedding divisor of level $1 \cdot p$. Let $e \ne e'$ be two edges. The assertion is: for every nonarchimedean absolute value $\mu$ on $\overline{\mathbb Q}$ with values in $\mathbb R$ such that $A = \{a : \mu(a) \le 1\}$, for all places $R$ in the domain of `Δ.annIn e` and $R'$ in the domain of `Δ.annIn e'`, if every place $Q$ of the domain of `Δ.annIn e` at which some member $t_l$ has nonzero order satisfies $\mu(Q(\,\cdot\,)) < \mu(R(\,\cdot\,))$ for the parameter of the outer annulus `Δ.annOut e` evaluated by `Place.evalAt`, and likewise at $e'$ with the parameter of `Δ.annOut e'`, and if the evaluation vectors `evalVec s R` and `evalVec s R'` are not proportional (there are indices $i', j'$ with $x_{i'}y_{j'} \ne x_{j'}y_{i'}$ for $x =$ `evalVec s R`, $y =$ `evalVec s R'`), then the chordal proximity $$\bigl|\,\log \sup_i \mu(x_i) + \log \sup_i \mu(y_i) - \log \sup_{(i,j)} \mu(x_i y_j - x_j y_i)\,\bigr| \le 4\bigl(\mathrm{linkBudget}(\Phi,s) + \mathrm{modulusExp}\bigr)\cdot\bigl(-\log \mu(p)\bigr).$$ Here $x_i = R\bigl(s_i\, s_{\mathrm{piv}}^{-1}\bigr)$ and $y_i = R'\bigl(s_i\, s_{\mathrm{piv}}^{-1}\bigr)$ are the normalised evaluation vectors at the respective pivot indices.
--
--   This is the cross-annulus case of the chordal separation estimate: two places lying in the tubes of distinct supersingular edges, each above all the zeros of the good family in its own tube as measured by the outer annulus parameter, are chordally separated by at most a fixed multiple of $-\log\mu(p)$. It feeds the variant [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent), in which the non-proportionality hypothesis is replaced by orthogonality and linear independence conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_outer.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.MultCovering
open AlgebraicCurve

theorem ModularCurve.MultCovering.crossComparison_annIn_annIn_of_outer (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∀ l : Fin r, ∀ Q ∈ (Δ.annIn e).dom, Q.ord (goodFamily Φ l) ≠ 0 →
            μ (Q.evalAt (Δ.annOut e).param) < μ (R.evalAt (Δ.annOut e).param)) →
        (∀ l : Fin r, ∀ Q ∈ (Δ.annIn e').dom, Q.ord (goodFamily Φ l) ≠ 0 →
            μ (Q.evalAt (Δ.annOut e').param) < μ (R'.evalAt (Δ.annOut e').param)) →
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by sorry
