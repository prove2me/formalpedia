-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom
-- name    : ModularCurve.MultCovering.abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/81f09cda-6671-503e-b273-2336fbf71868
-- title:
--   Good family bounded by μ(p)^{nᵢ} on the ̄ 0-chart
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$ (an algebraic closure of $\mathbb{Q}$) such that $p$, viewed in $\overline{\mathbb{Q}}$, is a nonunit of $A$, and whose residue field has characteristic $p$; let $\Gamma$ be a chart context for $p$ and $A$ (the package consisting of modular polynomial data at level one together with the Kronecker congruence, integrality of the Hecke operators $\bar\alpha,\bar\beta$, a place specialisation and its level-one prolongation pair, a set of places of the geometric modular function field of level $1\cdot p$, the finset of supersingular places, finiteness of the supersingular $j$-set with cardinality $\mathrm{mAnnuli}\,p$, and the chart supply), and let $\Phi$ be a family context of some length $r$, so that $\mathrm{goodFamily}\,\Phi$ is the family $\Phi.t$ of $r$ elements of the geometric modular function field of level $1\cdot p$. Then for every real absolute value $\mu$ on $\overline{\mathbb{Q}}$ whose unit ball is exactly $A$ (that is, $a \in A \iff \mu(a) \le 1$ for all $a$), and for every place $Q$ in the domain of the chart $\mathrm{zeroChart}\,\Gamma$ — the pullback of $\mathrm{infChart}\,\Gamma$ along the Fricke involution, so $Q$ lies in this domain precisely when its Fricke translate lies in the domain of $\mathrm{infChart}\,\Gamma$ — the place $Q$ is rational (the structure map from $\overline{\mathbb{Q}}$ to its residue field is surjective) and for each index $i < r$ the member $\mathrm{goodFamily}\,\Phi\,i$ lies in the valuation subring of $Q$ and its value $Q.\mathrm{evalAt}$ at that member satisfies $\mu\bigl(Q.\mathrm{evalAt}(\mathrm{goodFamily}\,\Phi\,i)\bigr) \le \mu(p)^{\,\mathrm{hasseExp}\,\Phi\,i}$, the exponent being the natural-number truncation of the Hasse content of the family at $i$.
--
--   This is the regularity-and-size estimate for the members of the good family on the $\bar 0$-chart of the prime-level covering: each member is regular at every place of the chart's domain and its value is bounded by $\mu(p)$ raised to the member's Hasse exponent, so members with positive exponent are topologically nilpotent there. It feeds the cross-comparison lemmas that match values on the $\bar 0$-chart with values on the annuli.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ModularCurve.MultCovering.abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ Q ∈ (zeroChart Γ).dom, Q.IsRational ∧ ∀ i : Fin r,
        goodFamily Φ i ∈ Q.toValuationSubring ∧
        μ (Q.evalAt (goodFamily Φ i)) ≤ μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData i := by sorry
