-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
-- name    : ModularCurve.MultCovering.abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/40f8c36c-18dc-599e-98b3-5f994af3c2e2
-- title:
--   Profile of a zero-free good-family member on an annulus
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (so that $p$ lies in the maximal ideal) and with residue field of characteristic $p$, let $\Gamma$ be a chart context `ChartCtx p A` for level $1\cdot p$, let $\Delta$ be an annulus context `AnnCtx` over $\Gamma$, let $\Phi$ be a family context `FamCtx p r`, let $e$ index one of the `mAnnuli p` annuli and let $l : \mathrm{Fin}\ r$. Assume that the family member $t_l=$ `goodFamily` $\Phi\ l$ lies in the integers of the chart `infChart` $\Gamma$, that the node place `nodeTgt` $\Gamma\ e$, i.e. the geometric level-one place of the residue field of $A$ at the supersingular value `ssValue` $\Gamma\ e$, takes order exactly $1$ on the `infChart` residue of $t_l$, and that $R.\mathrm{ord}(t_l)=0$ for every place $R$ in the domain of the annulus `Δ.annIn e`. Then for every real absolute value $\mu$ on $\overline{\mathbb{Q}}$ whose unit ball is exactly $A$, the following three assertions hold. First, $\mu(p)^{n_l}=\mu(\pi_e)$, where $n_l$ is the Hasse exponent `hasseExp` $\Phi.\mathrm{toFamData}\ l$ (the non-negative part of the minimal $p$-adic valuation of the coefficients of the associated zero series) and $\pi_e$ is the modulus of `Δ.annIn e`, an element of the maximal ideal of $A$, namely $p^{\mathrm{jWidth}(\mathrm{ssValue}\ \Gamma\ e)}$. Secondly, the rescaled member `goodFamilyZero` $\Phi.\mathrm{toFamData}\ l = p^{-n_l}t_l$ lies in the integers of the chart `zeroChart` $\Gamma$ (the pullback of `infChart` along the Fricke involution), and the node place `nodeSrc` $\Gamma\ e$, the geometric place at $(\mathrm{ssValue}\ \Gamma\ e)^p$, takes order $-1$ on its residue. Thirdly, every place $R$ in the domain of `Δ.annIn e` is rational (the structure map into its residue field is surjective), $t_l$ lies in the valuation subring of $R$, and the values at $R$ satisfy $\mu(R.\mathrm{evalAt}\ t_l)=\mu(R.\mathrm{evalAt}\ z_e'')$ and $\mu(\pi_e)<\mu(R.\mathrm{evalAt}\ z_e'')$, where $z_e''$ is the parameter of the companion annulus `Δ.annOut e`.
--
--   This is the two-slope analysis of a member of the good family on a supersingular annulus of the multiplicative covering of level $1\cdot p$: it pins down the Hasse exponent by the annulus modulus, the order of the rescaled member at the opposite node, and the absolute value of the member at each place of the annulus. It is used by the cross-comparison lemmas relating values on two annuli, and on an annulus and the zero-chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero.lean

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

theorem ModularCurve.MultCovering.abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p)) (l : Fin r)
    (hint : goodFamily Φ l ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hzf : ∀ R ∈ (Δ.annIn e).dom, R.ord (goodFamily Φ l) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l = μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) ∧
      (∃ h0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, h0⟩) = -1) ∧
      ∀ R ∈ (Δ.annIn e).dom,
        R.IsRational ∧ goodFamily Φ l ∈ R.toValuationSubring ∧
        μ (R.evalAt (goodFamily Φ l)) = μ (R.evalAt (Δ.annOut e).param) ∧
        μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) < μ (R.evalAt (Δ.annOut e).param) := by sorry
