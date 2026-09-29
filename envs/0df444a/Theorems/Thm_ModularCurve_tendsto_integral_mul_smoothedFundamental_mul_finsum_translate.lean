-- Prove2me | Theorems.Thm_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate
-- name    : ModularCurve.tendsto_integral_mul_smoothedFundamental_mul_finsum_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/48b973f7-c83d-5696-9a07-c94f5bd66502
-- title:
--   Smoothed unfolding of a weight-two pairing against F
-- statement:
--   Let $\Gamma$ be a subgroup of $SL_2(\mathbb Z)$ of finite index, let $F:\mathbb C\to\mathbb C$ be continuous with compact support whose topological support is contained in $\{z:\operatorname{Im}z>0\}$, and let $g:\mathfrak H\to\mathbb C$ be continuous and satisfy $g(\gamma\cdot\tau)=\operatorname{denom}(\gamma,\tau)^2\,g(\tau)$ for all $\gamma\in\Gamma$ and all $\tau\in\mathfrak H$, where $\operatorname{denom}(\gamma,\tau)=c\tau+d$ for $\gamma$ viewed in $GL_2(\mathbb R)$. Let $h:\mathbb R\to\mathbb C\to\mathbb C$ be such that $h(T,z)$ is the complex number attached to $\mathrm{smoothedFundamental}\ \Gamma\ T\ z$, that is to the real sum $\sum_{q\in SL_2(\mathbb Z)/\Gamma}\mathrm{puCut}\,T\,(\mathrm{mob}\,(\mathrm{out}\,q)\,z)$, with $\mathrm{mob}\,\delta\,z=\mathrm{num}(\delta,z)/\operatorname{denom}(\delta,z)$ and $\mathrm{puCut}\,T\,z=\mathrm{pu}\,T\,z\cdot\mathrm{gcut}\,T\,z$, the sum taken over a choice of representative $\mathrm{out}\,q$ of each coset. Write $P(z)=\sum_{\gamma\in\Gamma}F(\gamma\cdot\mathrm{ofComplex}\,z)\,\overline{\operatorname{denom}(\gamma,\mathrm{ofComplex}\,z)^{-2}}$, a possibly infinite sum over $\Gamma$, where $\mathrm{ofComplex}$ is the retraction of $\mathbb C$ onto $\mathfrak H$ agreeing with the identity on the upper half-plane. The assertion is twofold: for every real $T$ the function $z\mapsto g(\mathrm{ofComplex}\,z)\,h(T,z)\,P(z)$ is integrable on $\mathbb C$, and as $T\to\infty$ its integral over $\mathbb C$ converges to $\int_{\mathbb C}g(\mathrm{ofComplex}\,z)\,F(z)$.
--
--   This is the Rankin–Selberg unfolding identity in smoothed form: the $\Gamma$-periodisation $P$ of a compactly supported $(0,1)$-density, paired with a weight-two function $g$ and cut off by the smoothed fundamental function at height $T$, has integral tending to the plane integral of $gF$. It is used in the construction of invariant local models and of the winding pairing, being cited by [`ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental`](thm.html#ModularCurve.exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental) and its period variant; the properties of the cutoff enter through [`ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one`](thm.html#ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one), which gives smoothness, compact support in the upper half-plane, local finiteness of the $\Gamma$-translates, and the bound $\sum_{\gamma\in\Gamma}h_T(\gamma\tau)\le 1$ with equality when $\max(\operatorname{Im}\tau,(\operatorname{Im}\tau)^{-1})\le T$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.tendsto_integral_mul_smoothedFundamental_mul_finsum_translate
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (F : ℂ → ℂ) (hF : Continuous F) (hFs : HasCompactSupport F)
    (hFU : tsupport F ⊆ {z : ℂ | 0 < z.im})
    (g : ℍ → ℂ) (hg : Continuous g)
    (hgw : ∀ γ ∈ Γ, ∀ τ : ℍ, g (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * g τ)
    (h : ℝ → ℂ → ℂ) (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental Γ T z : ℂ)) :
    (∀ T : ℝ, Integrable fun z : ℂ => g (ofComplex z) * h T z *
        ∑ᶠ γ : Γ, F (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
          conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2)) ∧
    Tendsto (fun T : ℝ => ∫ z : ℂ, g (ofComplex z) * h T z *
        ∑ᶠ γ : Γ, F (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
          conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2)) atTop
      (𝓝 (∫ z : ℂ, g (ofComplex z) * F z)) := by sorry
