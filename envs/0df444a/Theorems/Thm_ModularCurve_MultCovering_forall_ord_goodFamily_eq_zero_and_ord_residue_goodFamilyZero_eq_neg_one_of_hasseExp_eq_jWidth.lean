-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth
-- name    : ModularCurve.MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/23aaefb1-798e-5afc-a0a9-0e880d80855b
-- title:
--   Hasse exponent equal to node width forces a simple pole
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$, in the sense that $p$ belongs to the non-units of $A$, with residue field of characteristic $p$; let $\Gamma$ be a chart context for the prime level $1\cdot p$ over $A$ and $\Delta$ an annulus context over $\Gamma$. Fix $r$, a good-family context $\Phi$ of rank $r$, an index $e$ among the $\mathrm{mAnnuli}\,p$ annuli, and a member index $l$. Assume: the Hasse exponent $\mathrm{hasseExp}\,\Phi\,l$ (the non-negative part of the minimal $p$-adic valuation of the coefficients of the associated zero series) equals $\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)$, which is $3$, $2$ or $1$ according as the supersingular value $\mathrm{ssValue}\,\Gamma\,e$ is $0$, is $1728$, or is neither; the member $t_l = \mathrm{goodFamily}\,\Phi\,l$ lies in the integers of the chart $\mathrm{infChart}\,\Gamma$, and its residue has order exactly $1$ at $\mathrm{nodeTgt}\,\Gamma\,e$, the place of the level-one geometric function field over the residue field of $A$ attached to the point $\mathrm{ssValue}\,\Gamma\,e$. Assume finally that $\mu$ is a real absolute value on $\overline{\mathbb Q}$ with $A = \{a : \mu(a) \le 1\}$. Then $t_l$ has order $0$ at every place in the domain of the annulus $\Delta.\mathrm{annIn}\,e$, and the rescaled member $\mathrm{goodFamilyZero}\,\Phi\,l = p^{-\mathrm{hasseExp}\,\Phi\,l}\,t_l$ lies in the integers of $\mathrm{zeroChart}\,\Gamma$ and its residue has order $-1$ at $\mathrm{nodeSrc}\,\Gamma\,e$, the place attached to $(\mathrm{ssValue}\,\Gamma\,e)^p$.
--
--   This is the equality case of the two-end law for an annulus attached at both ends to the two components of the mod $p$ fibre: when the $p$-adic rescaling exponent of a family member matches the width $p^{w_e}$ of the annulus, the member is zero-free on the annulus and the rescaled member acquires a simple pole at the node on the opposite component. It feeds the cross-comparison results [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_eq_eleven`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_eq_eleven), [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent) and [`ModularCurve.MultCovering.crossComparison_annIn_zeroChart`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_zeroChart), covering the wide nodes $w_e \in \{2,3\}$ alongside the width-one case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p)) (l : Fin r)
    (hn : hasseExp Φ.toFamData l = jWidth (ssValue Γ e))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    (∀ R ∈ (Δ.annIn e).dom, R.ord (goodFamily Φ l) = 0) ∧
      ∃ h0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, h0⟩) = -1 := by sorry
