-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge
-- name    : ModularCurve.MultCovering.mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/06b33ccd-13d2-5d72-b189-92162730cbc1
-- title:
--   Reduced good family spans the width-one polar system
-- statement:
--   Let $p\ge 5$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$, in the sense that $p$ belongs to the nonunits of $A$, with residue field $k=\mathrm{ResidueField}\,A$ of characteristic $p$. Let $\Gamma$ be a chart context for $(p,A)$ — modular polynomial data with its Kronecker congruence, integrality of the Hecke coefficients $\bar\alpha,\bar\beta$ at level $1$, a place specialisation over $A$ together with a level-one prolongation pair, a set $S_1$ of places of $\overline{\mathbb Q}$-level $p$ modular functions, the finite set $W_n$ of supersingular places at level $1$ over $k$, and the finiteness of the supersingular $j$-set with cardinality $m=\mathrm{mAnnuli}\,p$ — and let $\Delta$ be an annulus context for $\Gamma$, providing for each $e\in\mathrm{Fin}\,m$ a pair of annuli with common domain, modulus $p^{w_e}$ where $w_e=\mathrm{jWidth}(a_e)$ for $a_e=\mathrm{ssValue}\,\Gamma\,e$ (so $w_e=3,2,1$ according as $a_e=0$, $a_e=1728$, or neither), product of parameters equal to the modulus, and attachment to the charts at the nodes $\mathrm{nodeSrc}\,\Gamma\,e$ and $\mathrm{nodeTgt}\,\Gamma\,e$. Let $\Phi$ be a family context of rank $r$ for $p$, and write $t'_l=(p^{\mathrm{hasseExp}\,\Phi\,l})^{-1}\,\Phi.t\,l$ for its rescaled members. Assume each $t'_l$ lies in the integers of the chart $\mathrm{zeroChart}\,\Gamma$ (the pullback of $\mathrm{infChart}\,\Gamma$ along the Fricke involution at level $1\cdot p$) and that the residues $\overline{t'_l}$, $l\in\mathrm{Fin}\,r$, in the level-one modular function field $\mathrm{modularFunctionFieldC}\,k\,1$ are linearly independent over $k$. Let $f$ be an element of that field such that $\mathrm{ord}_v f\ge 0$ at every place $v$ over $k$ which is not a node of $\mathrm{zeroChart}\,\Gamma$, and such that for every $e$ one has $\mathrm{ord}_{\mathrm{nodeSrc}\,\Gamma\,e} f \ge -\lfloor 1/w_e\rfloor$, the quotient being natural-number division, i.e. $f$ has at most a simple pole at the node attached to $a_e$ when $w_e=1$ and is regular there when $w_e\ge 2$. Then $f$ lies in the $k$-span of the set of residues $\{\overline{t'_l} : l\in\mathrm{Fin}\,r\}$.
--
--   This is the spanning statement for the second component of the reduction of the covering of $X_0(p)$: the reductions of the rescaled good family exhaust the linear system of functions on that component with at most simple poles at the width-one nodes and no other poles. It is used in the computation of orders at the nodes on the zero chart and in assembling the chart data for the reduced good family, both in general and in the range $p<13$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (f : ↥(modularFunctionFieldC (ResidueField ↥A) 1))
    (hreg : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord f)
    (hnode : ∀ e : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e) : ℕ) : ℤ) ≤ (nodeSrc Γ e).ord f) :
    f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by sorry
