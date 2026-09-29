-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge
-- name    : ModularCurve.MultCovering.mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/7d0bf946-1a3d-547d-aa09-d5f537abe25a
-- title:
--   Members of Hasse content at most one span the narrow-node polar system
-- statement:
--   Let $p$ be a prime with $5 \le p$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ belongs to the nonunits of $A$; write $k$ for the residue field of $A$, assumed of characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A` for $p$ and $A$, let $\Delta$ be an annulus context `AnnCtx Γ` over it, and let $\Phi$ be a family context `FamCtx p r` for some $r$, with underlying family data $\Phi.\mathrm{toFamData}$ and members $t_l$, $l \in \mathrm{Fin}\,r$. Put $t'_l = (p^{n_l})^{-1} t_l$, where $n_l =$ `hasseExp Φ.toFamData l` is the truncation to $\mathbb{N}$ of the Hasse content of the $l$-th member; this is `goodFamilyZero Φ.toFamData l`. Assume: each $t'_l$ lies in the integers of the chart `zeroChart Γ`, the pullback of `infChart Γ` along the Fricke involution in level $1\cdot p$; and the $r$ residues $\overline{t'_l}$ of the $t'_l$ on that chart are linearly independent over $k$. Let $f$ be an element of the modular function field `modularFunctionFieldC k 1`, the subfield of $k((q))$ generated over $k$ by the level-one $q$-expansions `jqModC` and `jqNModC`. Assume further that $\mathrm{ord}_v f \ge 0$ for every place $v$ of this field over $k$ that is not a node of `zeroChart Γ`, and that for every $e$ among the $m_p = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$ indices one has $\mathrm{ord}_{x_e} f \ge -\lfloor 1/w_e \rfloor$, where $x_e =$ `nodeSrc Γ e` is the place of the source component at the point $a_e^{\,p}$, $a_e =$ `ssValue Γ e`, the width $w_e$ is `jWidth` of $a_e$, namely $3$ if $a_e = 0$, $2$ if $a_e = 1728$ and $1$ otherwise, and the floor is natural-number division, so the bound is $-1$ at nodes of width one and $0$ at the nodes of width $2$ and $3$. Then $f$ lies in the $k$-span of the set of residues $\overline{t'_l}$ taken over those $l$ with $n_l \le 1$.
--
--   This is the spanning statement for the reduced good family on the component cut out by `zeroChart Γ` in the multiplicative-reduction covering of $X_0(p)$: the members of Hasse content at most one, together with the constant member, exhaust the space of functions on that component regular away from the nodes and with at most simple poles at the nodes of width one. It is used in the construction of a family member of content exactly one that is unramified and separates the relevant nodes, and in the two-member certificate produced when some supersingular value is $0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge.lean

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

theorem ModularCurve.MultCovering.mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge
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
        (Set.range fun l : {l : Fin r // hasseExp Φ.toFamData l ≤ 1} =>
          (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by sorry
