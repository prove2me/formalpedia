-- Prove2me | Theorems.Thm_ModularCurve_intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul
-- name    : ModularCurve.intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/d07b5026-8a7d-521a-88d6-5f6e8f16314f
-- title:
--   Nonvanishing mod p of q-expansions at cusps γ∞
-- statement:
--   Let $p$ be a prime and $M \ge 1$ a natural number with $p \mid M$ and $p^2 \nmid M$. Let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial, and let $K$ be a field of characteristic $p$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$, let $k$ be an integer, and let $h, h_1$ be modular forms of weight $k$ for the subgroup of $\mathrm{GL}_2(\mathbb{R})$ determined by [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the matrices of $\Gamma_0(M)$ whose lower-right entry, read modulo $M$ as a unit, lies in $H$. Let $ph, ph_1$ be power series with integer coefficients which are integral $q$-expansions of $h$ and $h_1$, in the sense that pushing their coefficients into $\mathbb{C}$ yields the width-one $q$-expansions of $h$ and of $h_1$ respectively, and assume $h_1 = h \mid_k \gamma$ as functions on the upper half-plane. If the Laurent series over $K$ obtained by reducing the coefficients of $ph$ along $\mathbb{Z} \to K$ is nonzero, then the same holds for $ph_1$.
--
--   This is the $q$-expansion principle modulo $p$ along the cusps $\gamma\infty$ with $\gamma \in \Gamma_0(M)$: for $\Gamma_H(M)$-forms with $p$ exactly dividing $M$ and $H$ containing the kernel of reduction to level $M/p$, nonvanishing modulo $p$ of the expansion at $\infty$ propagates to the expansion at any such cusp, equivalently under the diamond operator $\langle d\rangle$ given by the lower-right entry of $\gamma$. It is used in the treatment of diamond operators on $q$-expansions modulo $p$, in particular by [`CuspForm.forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt`](thm.html#CuspForm.forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt) and by [`ModularCurve.IsDiamondPullbackModL.coe_apply_eq_of_mem_Gamma0_of_level_mul`](thm.html#ModularCurve.IsDiamondPullbackModL.coe_apply_eq_of_mem_Gamma0_of_level_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [CharP K p]
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (k : ℤ) (h h₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (ph ph₁ : PowerSeries ℤ)
    (hh : ModularCurve.IsIntegralQExp h ph) (hh₁ : ModularCurve.IsIntegralQExp h₁ ph₁)
    (hhs : (⇑h₁ : UpperHalfPlane → ℂ) = ((⇑h : UpperHalfPlane → ℂ) ∣[k] γ))
    (h0 : ModularCurve.intSeriesC K ph ≠ 0) :
    ModularCurve.intSeriesC K ph₁ ≠ 0 := by sorry
