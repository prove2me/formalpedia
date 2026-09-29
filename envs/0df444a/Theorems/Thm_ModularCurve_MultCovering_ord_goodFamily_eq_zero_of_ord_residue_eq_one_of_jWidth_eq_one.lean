-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one
-- name    : ModularCurve.MultCovering.ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/4dfd0b22-fb05-5ff0-85ac-aae37c99dc48
-- title:
--   Good-family members have no zeros on a width-one supersingular tube
-- statement:
--   Fix a prime $p$ and a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` such that $p$ is a nonunit of $A$ (`A.LiesOverPrime p`), with residue field of characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A` for the multiplicative covering at level $1 \cdot p$, and $\Delta : \mathrm{AnnCtx}\ \Gamma$ the associated annulus data, consisting of two annuli $\mathrm{An}\ e$, $\mathrm{An}'\ e$ for each index $e$ in `Fin (mAnnuli p)` with common domain and modulus $p^{\mathrm{jWidth}(\mathrm{ssValue}\ \Gamma\ e)}$, product of parameters equal to the modulus, domain consisting exactly of the places supersingularly centred at $\mathrm{ssValue}\ \Gamma\ e$, and attachment to the charts at the nodes $\mathrm{nodeSrc}\ \Gamma\ e$, $\mathrm{nodeTgt}\ \Gamma\ e$. Let $\Phi$ be a family context `FamCtx p r`, with underlying functions $t_l = \mathrm{goodFamily}\ \Phi\ l$ in $\overline{\mathcal{F}}(1\cdot p)$. Assume $\mathrm{jWidth}(\mathrm{ssValue}\ \Gamma\ e) = 1$, that is, the supersingular value $\mathrm{ssValue}\ \Gamma\ e$ is neither $0$ nor $1728$, so the modulus of the annuli at $e$ is $p$ itself. Let $l$ be an index with $1 \le l$ such that $t_l$ lies in the valuation subring $(\mathrm{infChart}\ \Gamma).\mathrm{integers}$ and such that its reduction $(\mathrm{infChart}\ \Gamma).\mathrm{residue}\ t_l$ has order exactly $1$ at the place $\mathrm{nodeTgt}\ \Gamma\ e$ of the geometric residue field, the place attached to the point $\mathrm{ssValue}\ \Gamma\ e$. Then for every place $R$ in the domain of $\Delta.\mathrm{annIn}\ e = \mathrm{An}\ e$ one has $\mathrm{ord}_R(t_l) = 0$, where $\mathrm{ord}$ denotes minus the logarithm of the adic valuation of the place.
--
--   This is the statement that a member of the good family of index $\ge 1$ whose $\overline{\infty}$-chart reduction has a simple zero at a width-one supersingular node has no zeros at all on the corresponding supersingular tube; the hypothesis on the width means the node is neither at $j = 0$ nor at $j = 1728$, so the tube has modulus $p$. It feeds the cross-comparison estimates between the tube at $e$ and the neighbouring annuli and the zero chart, among them [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one) and [`ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_adapted`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_zeroChart_of_adapted).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one.lean

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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ModularCurve.MultCovering.ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p)) (hw : jWidth (ssValue Γ e) = 1) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1) :
    ∀ R ∈ (Δ.annIn e).dom, R.ord (goodFamily Φ l) = 0 := by sorry
