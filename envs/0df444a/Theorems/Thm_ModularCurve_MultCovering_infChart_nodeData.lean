-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_nodeData
-- name    : ModularCurve.MultCovering.infChart_nodeData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/a322fa16-7b8e-5d60-9228-5cb0643643b9
-- title:
--   Node data for the good family on the ∞̄-chart
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (the hypothesis `A.LiesOverPrime p`), and suppose the residue field of $A$ has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, that is, modular polynomial data at level $p$ together with its Kronecker congruence, integrality of the two Hecke coefficient maps $\bar\alpha,\bar\beta$ at level $1$, a place specialisation $P$ over $A$ with a level-one prolongation pair $R$, a set $S_1$ of places of the level-$p$ function field $\overline{\mathcal{F}}(1\cdot p)$, a finset $W_n$ of places of the level-one function field over the residue field consisting exactly of the supersingular places, and the data that the supersingular $j$-set is finite of cardinality $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p\equiv 2 \bmod 3] + [p\equiv 3 \bmod 4]$, plus the chart supply condition. Let $r$ be a natural number and $\Phi$ a family context `FamCtx p r`, whose underlying functions $t_l =$ `goodFamily` $\Phi\, l$ form an embedding basis. The assertion is that all $t_l$ lie in the valuation ring `(infChart Γ).integers` of the $\bar\infty$-chart and that, for every index $e$ of the $\mathrm{mAnnuli}\,p$ nodes, writing $\bar t_l$ for the image of $t_l$ under the chart's residue map and $\mathrm{ord}$ for the order function of the place `nodeTgt Γ e` (the geometric place of the level-one function field over the residue field at the supersingular value $\mathrm{ssValue}\,\Gamma\,e$): first, $\mathrm{ord}(\bar t_l)\ge 1$ for every $l$ with $1\le l$; and second, there is some $l$ with $1\le l$ and $\mathrm{ord}(\bar t_l) = 1$. The pivot index $l$ in the second clause may depend on the node $e$.
--
--   This records the local behaviour at the supersingular nodes of the reductions, on the $\bar\infty$-component chart, of the members of the good family indexed by $l\ge 1$: each vanishes to order at least one at each node, and at each node some member vanishes to order exactly one. It is one of the inputs to the comparison of the $\bar 0$- and $\bar\infty$-charts, used by the cross-comparison statements about the zero chart and by the construction separating nodes with Hasse exponent one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_nodeData.lean

import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.infChart_nodeData (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∃ hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers,
      ∀ e : Fin (mAnnuli p),
        (∀ l : Fin r, 1 ≤ (l : ℕ) →
          1 ≤ (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩)) ∧
        (∃ l : Fin r, 1 ≤ (l : ℕ) ∧
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩) = 1) := by sorry
