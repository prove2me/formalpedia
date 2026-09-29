-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes
-- name    : ModularCurve.MultCovering.zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/8ab196dc-3cb6-568e-bc64-bcdd10812604
-- title:
--   Rescaled good family reduces to functions regular off the nodes
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a nonunit of $A$, with residue field $k$ of characteristic $p$, and let $\Gamma$ be a chart context for $p$ and $A$ (modular polynomial data together with its Kronecker congruence, integrality of the Hecke $\bar\alpha$- and $\bar\beta$-operators at level $1$, a place specialisation and a level-one prolongation pair, a set $S_1$ of places of $\overline{\mathbb{Q}}$-modular functions of level $1\cdot p$, the finite set of supersingular places, finiteness of the supersingular $j$-set with exactly $\mathrm{mAnnuli}\,p$ elements, and a chart supply; these data are summarised here). Let $r$ be a natural number and $\Phi$ a family context of rank $r$ for $p$, with underlying family data $\Phi.\mathrm{toFamData}$, whose $l$-th rescaled member is $\mathrm{goodFamilyZero}\,\Phi.\mathrm{toFamData}\,l = p^{-\mathrm{hasseExp}\,\Phi\,l}\,\Phi.t\,l$ in the field $\overline{\mathbb{Q}}$-modular functions of level $1\cdot p$. The assertion is that there is a witness showing that every such element lies in the valuation subring of chart integers of $\mathrm{zeroChart}\,\Gamma$, the component chart obtained from $\mathrm{infChart}\,\Gamma$ by pulling back along the Fricke involution, and that, with respect to that witness, for every $l \in \mathrm{Fin}\,r$ and every place $v$ of the function field $\mathrm{modularFunctionFieldC}\,k\,1$ over $k$ (a proper valuation subring containing $k$ whose ideals are principal) which does not belong to the finite set of nodes of $\mathrm{zeroChart}\,\Gamma$, one has $0 \le \mathrm{ord}_v$ of the chart residue of that element.
--
--   This is the $\bar 0$-chart counterpart of the regularity statement for the good family on the $\bar\infty$-chart: the $p$-power rescalings $p^{-n_l}t_l$ are chart units on the zero chart whose only pole lies outside its domain, so their reductions are regular at every non-nodal place of the $\bar 0$-line. It is used in the subsequent analysis of the Hasse exponents $\mathrm{hasseExp}\,\Phi\,l$ and of the orders of the reductions at the nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      ∀ (l : Fin r) (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)),
        v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by sorry
