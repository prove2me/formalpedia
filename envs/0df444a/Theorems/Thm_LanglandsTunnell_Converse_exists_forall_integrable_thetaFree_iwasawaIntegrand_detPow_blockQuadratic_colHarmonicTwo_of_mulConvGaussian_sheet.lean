-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/1f95f5d1-7395-5b30-8c4f-b243b9ef2af8
-- title:
--   Integrability of the θ-free Iwasawa integrand for a quadratic section
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb{C}$, $b\in\mathbb{Z}/2$ and a function $W:\mathbb{R}\to\mathbb{C}$ continuous on $\{t\neq0\}$ which is $(-1)^b$-parity equivariant, $W(-t)=(-1)^{b}W(t)$, and satisfies for every $t>0$ the one-sheet identity $W(t)+(-1)^{b}W(-t)=4t\int_{0}^{\infty}r^{\nu_1}e^{-\pi r^2}(t/r)^{\nu_2}e^{-\pi(t/r)^2}\,\frac{dr}{r}$. Fix further a real archimedean parameter $P_2$ (principal or discrete), an archimedean Whittaker datum $D$ for $P_2$ (a function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with $D.W(u(x)g)=e^{2\pi i x}D.W(g)$ and the central law for $\chi_{P_2}$, together with entire zeta functions, their functional equation, finite order and decay at $0$ and $\infty$), a real $a\neq0$, complex $u_0$, $c_P$, a sign character exponent $a_0\in\mathbb{Z}/2$, and $\delta\in\{0,1\}$. The conclusion asserts the existence of $\sigma\in\mathbb{R}$ such that for all $s$ with $\operatorname{Re}s>\sigma$ the function of $(x,y_1,y_2)$ given by $$\chi_{u_0,a_0}\!\big((y_1y_2)^{-1}\big)\,|y_1y_2|^{2}\cdot\chi_{P_2}(y_2)|y_2|\cdot\Big(\int_{\mathbb{R}}W(t)\,e^{2\pi i a t x}\,D.W\!\big(\operatorname{diag}(aty_1/y_2,1)\big)|t|^{s-1/2}t^{-2}\,dt\Big)$$ multiplied by $(y_1y_2)^{-\delta}\big[\tfrac{1+x^2}{y_1^2}-\tfrac{1}{y_2^2}-\tfrac{2ix}{y_1y_2}\big]e^{-\pi(\frac{1+x^2}{y_1^2}+\frac{1}{y_2^2})}|y_1y_2|\,(-ia)^2(-iy_2)^2\cdot\tfrac12(\pi a^2y_2^2)^{-(c_P+\chi\text{-exponent}(P_2)+2s+3)/2}\Gamma\big(\tfrac{c_P+\chi\text{-exponent}(P_2)+2s+3}{2}\big)$ and by $y_2^2|y_1y_2|^{-4}$, where $\chi_{u,a}(y)=|y|^{u}$ times $\operatorname{sign}(y)$ when $a\neq0$ and $\chi$-exponent$(P_2)$ is the central exponent $u_1+u_2$ (resp. $2u$), is integrable on $\mathbb{R}\times\mathbb{R}\times(0,\infty)$ for Lebesgue measure, the last factor restricted to $(0,\infty)$. The parameters $\nu_1,\nu_2$ enter only through the displayed Gaussian-convolution identity for $W$.
--
--   This is the absolute-convergence input for the archimedean Rankin–Selberg computation in the converse-theorem route: the $\theta$-free Iwasawa-coordinate integrand attached to the quadratic Schwartz section $\det^{\delta}(z_0^2+z_1^2)$ times a degree-two column harmonic and a Gaussian, with a weight $W$ of one-sheet Gaussian-convolution type. It is used by the unfolding identity [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile), where integrability licenses the interchange of the torus and Tate integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
        ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * q.1) * D.W (ArchR.diagOne (a * t * q.2.1 / q.2.2)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ)) ^ δ *
              ((((1 + q.1 ^ 2) / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * q.1 / (q.2.1 * q.2.2) : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + q.1 ^ 2) / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) *
              ((|q.2.1 * q.2.2| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (q.2.2 : ℂ)) ^ 2 *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
