-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul
-- name    : ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/99099fd8-4adb-5cad-9953-95548420ae4e
-- title:
--   Equality case: zero-free supersingular annulus, opposite node orders
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that the image of $p$ is a non-unit of $A$, with residue field of characteristic $p$. Let $\Gamma$ be a chart context for $p$ and $A$, let $\Delta$ be an annulus context over $\Gamma$, and let $e$ be one of the $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$ indices, with associated supersingular residue value $a_e = \mathrm{ssValue}\,\Gamma\,e$ in the residue field of $A$; the two distinguished places of the geometric level-one function field over that residue field are $\mathrm{nodeTgt}\,\Gamma\,e$, attached to the point $a_e$, and $\mathrm{nodeSrc}\,\Gamma\,e$, attached to $a_e^{\,p}$. Let $h$ be an element of the geometric modular function field $\overline{\mathbb{Q}}$-base change at level $1\cdot p$ such that: $h$ lies in the integers of the chart $\mathrm{infChart}\,\Gamma$ and its residue there is nonzero; every place $W$ with $\mathrm{ord}_W h < 0$ equals the cusp $\mathrm{cuspInftyBar}(1\cdot p)$; for a natural number $n$, the function $p^{-n}h$ lies in the integers of $\mathrm{zeroChart}\,\Gamma$ (the pullback of $\mathrm{infChart}\,\Gamma$ along the Fricke involution) with nonzero residue; and the numerical equality $n = \mathrm{jWidth}(a_e)\cdot \mathrm{ord}_{\mathrm{nodeTgt}\,\Gamma\,e}(\overline{h})$ holds, where $\mathrm{jWidth}(j)$ is $3$ for $j=0$, $2$ for $j=1728$ and $1$ otherwise, and $\overline{h}$ denotes the $\mathrm{infChart}$-residue of $h$. Then, first, $\mathrm{ord}_Q h = 0$ for every place $Q$ in the domain of the annulus $\Delta.\mathrm{An}\,e$, that is, for every place centred at the supersingular value $a_e$; and, second, the order of the $\mathrm{zeroChart}$-residue of $p^{-n}h$ at $\mathrm{nodeSrc}\,\Gamma\,e$ equals minus the order of $\overline{h}$ at $\mathrm{nodeTgt}\,\Gamma\,e$.
--
--   This is the equality (extremal) case of the two-end estimate for an annulus of the model of $X_0(p)$ over $A$: when the power of $p$ needed to make $h$ integral on the chart at $0$ is exactly the width of the supersingular annulus times the order of $\overline{h}$ at the corresponding node, the divisor of $h$ on the annulus must be empty and the order at the far node is the negative of the order at the near one. It is used in the construction of unimodular family data with wide certificates, where tight pole orders on the chart at the cusp $0$ are required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul.lean

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

theorem ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (e : Fin (mAnnuli p)) (h : ↥(modularFunctionFieldBar (1 * p))) (hC : h ∈ (infChart Γ).integers)
    (hres : (infChart Γ).residue ⟨h, hC⟩ ≠ 0)
    (hfpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W.ord h < 0 → W = cuspInftyBar (1 * p))
    (n : ℕ) (hC' : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ n))⁻¹ * h
      ∈ (zeroChart Γ).integers)
    (hres' : (zeroChart Γ).residue ⟨_, hC'⟩ ≠ 0)
    (hna : (n : ℤ) = (jWidth (ssValue Γ e) : ℤ) * (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩)) :
    (∀ Q ∈ (Δ.annIn e).dom, Q.ord h = 0) ∧
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨_, hC'⟩) = - (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩) := by sorry
