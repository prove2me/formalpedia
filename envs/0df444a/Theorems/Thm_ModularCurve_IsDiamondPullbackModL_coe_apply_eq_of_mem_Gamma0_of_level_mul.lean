-- Prove2me | Theorems.Thm_ModularCurve_IsDiamondPullbackModL_coe_apply_eq_of_mem_Gamma0_of_level_mul
-- name    : ModularCurve.IsDiamondPullbackModL.coe_apply_eq_of_mem_Gamma0_of_level_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/6cb035ab-c2e4-55ec-bc07-1aa23acbeb4e
-- title:
--   Pull-back formula for the reduced diamond action at level M
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ and $p^2 \nmid M$, and write $N = M/p$. Let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit that reduces to $1$ in $(\mathbb{Z}/N)^\times$, and let $H' =$ [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246) be the image of $H$ under `ZMod.unitsMap` for $N \mid M$. Let $K$ be an algebraically closed field of characteristic $p$. For a subgroup $\Gamma \le \mathrm{SL}(2,\mathbb{Z})$, [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) is the intermediate field of $K((q)) =$ `LaurentSeries K` generated over $K$ by the ratios $\overline{P}/\overline{Q}$, where $P,Q \in \mathbb{Z}[[q]]$ are integral $q$-expansions (in the sense that their images in $\mathbb{C}[[q]]$ are the width-one $q$-expansions) of two modular forms of one and the same weight on $\Gamma$, $\overline{\,\cdot\,}$ denotes coefficientwise reduction to $K$ viewed as a Laurent series, and $\overline{Q} \ne 0$; here [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) is the image in $\mathrm{SL}(2,\mathbb{Z})$ of the subgroup of $\Gamma_0(M)$ whose lower-right entry lies in $H$ modulo $M$. Let $\rho$ be a homomorphism from $\Gamma_0(N)$ to the group of $K$-algebra automorphisms of [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')`](def/ModularCurve_X1.html#L101) satisfying [`ModularCurve.IsDiamondPullbackModL`](def/ModularCurve_XHDiamondModL.html#L12), i.e. the level-$N$ pull-back formula: for every $\delta \in \Gamma_0(N)$, every weight $k$, and all weight-$k$ forms $f,g,f_1,g_1$ on [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) with integral $q$-expansions $P_f,P_g,P_{f_1},P_{g_1}$ such that $f_1 = f \mid_k \delta$, $g_1 = g \mid_k \delta$ and $\overline{P_g} \ne 0$, the automorphism $\rho(\delta)$ carries the element with Laurent series $\overline{P_{f_1}}/\overline{P_{g_1}}$ to the element with Laurent series $\overline{P_f}/\overline{P_g}$. Let $\gamma \in \Gamma_0(N)$ whose underlying matrix lies in $\Gamma_0(M)$, let $k \in \mathbb{Z}$, and let $h,h',h_1,h'_1$ be weight-$k$ modular forms on [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) with integral $q$-expansions $P_h,P_{h'},P_{h_1},P_{h'_1}$, such that $h_1 = h \mid_k \gamma$ and $h'_1 = h' \mid_k \gamma$ as functions on the upper half-plane, and assume $\overline{P_{h'}} \ne 0$. Then for every element $x$ of [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')`](def/ModularCurve_X1.html#L101) whose Laurent series is $\overline{P_{h_1}}/\overline{P_{h'_1}}$, the Laurent series of $\rho(\gamma)x$ is $\overline{P_h}/\overline{P_{h'}}$.
--
--   This is the slash-reduction step showing that the pull-back formula characterising the reduced diamond action on the $q$-expansion function field of the component through $\infty$, imposed at level $N = M/p$, automatically holds for the forms of level $\Gamma_H(M)$ when the matrix is taken in $\Gamma_0(M)$; it rests on the fact that $H$ contains the kernel of $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/N)^\times$, so that $\Gamma_H(M) = \Gamma_{H'}(N) \cap \Gamma_0(p)$. It is used in the computation of the action of the reduced diamond operators on differentials, via [`ModularCurve.diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet`](thm.html#ModularCurve.diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsDiamondPullbackModL_coe_apply_eq_of_mem_Gamma0_of_level_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.IsDiamondPullbackModL.coe_apply_eq_of_mem_Gamma0_of_level_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    {ρ : CongruenceSubgroup.Gamma0 (M / p) →*
      (ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))}
    (hρ : ModularCurve.IsDiamondPullbackModL K (M / p) (ModularCurve.infSubgroup p M H hpM) ρ)
    (γ : CongruenceSubgroup.Gamma0 (M / p)) (hγ : (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M)
    (k : ℤ) (h h' h₁ h'₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (ph ph' ph₁ ph'₁ : PowerSeries ℤ)
    (hh : ModularCurve.IsIntegralQExp h ph) (hh' : ModularCurve.IsIntegralQExp h' ph')
    (hh₁ : ModularCurve.IsIntegralQExp h₁ ph₁) (hh'₁ : ModularCurve.IsIntegralQExp h'₁ ph'₁)
    (hhs : (⇑h₁ : UpperHalfPlane → ℂ) = ((⇑h : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hh's : (⇑h'₁ : UpperHalfPlane → ℂ) = ((⇑h' : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hph' : ModularCurve.intSeriesC K ph' ≠ 0)
    (x : ModularCurve.qExpFunctionFieldC K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hx : (x : LaurentSeries K) = ModularCurve.intSeriesC K ph₁ / ModularCurve.intSeriesC K ph'₁) :
    ((ρ γ x : ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) =
      ModularCurve.intSeriesC K ph / ModularCurve.intSeriesC K ph' := by sorry
