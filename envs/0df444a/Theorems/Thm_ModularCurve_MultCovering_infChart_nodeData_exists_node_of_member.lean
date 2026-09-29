-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member
-- name    : ModularCurve.MultCovering.infChart_nodeData_exists_node_of_member
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/22a82b14-40f7-5a21-b63f-243dc702480f
-- title:
--   Each Hasse member is simple at some node
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (the hypothesis `LiesOverPrime`, i.e. the image of $p$ lies in `A.nonunits`), and let the residue field of $A$ have characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, which packages modular polynomial data at $p$ together with its Kronecker congruence, integrality of the $\bar\alpha$- and $\bar\beta$-Hecke maps at level $1$ and prime $p$, a place specialisation of $A$ with a level-one prolongation pair, a set $S_1$ of places of the base-changed modular function field of level $1\cdot p$, a finite set of places of the characteristic-$p$ level-one function field which is exactly the supersingular one, the finiteness of the supersingular $j$-set together with the equality of its cardinality with $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p\equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$, and the supply datum for the first chart; and let $\Phi$ be a family context `FamCtx p r`, whose underlying functions $t_l \in \overline{\mathcal{F}}_{1\cdot p}$ ($l \in \mathrm{Fin}\,r$) are written $\mathrm{goodFamily}\,\Phi$. The assertion is that all the $t_l$ lie in the valuation subring $(\mathrm{infChart}\,\Gamma).\mathrm{integers}$ and that, for this membership, every index $l$ with $l \ge 1$ admits an $e \in \mathrm{Fin}(\mathrm{mAnnuli}\,p)$ for which the reduction $(\mathrm{infChart}\,\Gamma).\mathrm{residue}(t_l)$ has order exactly $1$ at the node place $\mathrm{nodeTgt}\,\Gamma\,e$, the geometric place of the residue field of $A$ attached to the supersingular value $\mathrm{ssValue}\,\Gamma\,e$.
--
--   On the $\bar\infty$-component chart of the multiplicative covering, the reduction of $t_l$ for $l \ge 1$ is the Hasse (supersingular) polynomial times $P_l(\bar\jmath)$ with $\deg P_l < \mathrm{mAnnuli}\,p$, so $P_l$ cannot vanish at all supersingular values; at a value where it does not, the order of vanishing is exactly $1$. The result feeds the node rows of the cross-chart comparison, among them the bounds on the Hasse exponent and the zero-chart integrality statements for the good family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member.lean

import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.infChart_nodeData_exists_node_of_member (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∃ hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers,
      ∀ l : Fin r, 1 ≤ (l : ℕ) → ∃ e : Fin (mAnnuli p),
        (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩) = 1 := by sorry
