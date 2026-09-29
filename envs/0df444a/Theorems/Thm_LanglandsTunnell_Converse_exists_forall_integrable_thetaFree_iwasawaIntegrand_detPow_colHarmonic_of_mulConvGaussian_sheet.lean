-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_colHarmonic_of_mulConvGaussian_sheet
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_colHarmonic_of_mulConvGaussian_sheet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/488bb63c-8434-5343-9427-afe874773c88
-- title:
--   Integrability of the θ-free Iwasawa integrand, one Gaussian sheet
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb C$, a parity $b\in\mathbb Z/2$ and a function $W:\mathbb R\to\mathbb C$ that is continuous on $\{t\neq 0\}$, satisfies the single Gaussian-convolution relation $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_{0}^{\infty} r^{\nu_1}e^{-\pi r^{2}}(t/r)^{\nu_2}e^{-\pi (t/r)^{2}}\,\frac{dr}{r}$ for all $t>0$, and the parity law $W(-t)=(-1)^{b}W(t)$ for all $t$. Fix a real archimedean parameter $P_2$ (principal or discrete) and an archimedean Whittaker datum $D$ for $P_2$, i.e. a smooth function $D.W$ on $2\times2$ real matrices transforming under unipotents by $\psi(x)=e^{2\pi i x}$ and under the centre by $\omega_{P_2}(z)|z|$, with entire zeta functions satisfying the functional equation, finite order and the prescribed decay at $0$ and $\infty$. Fix $a\in\mathbb R$, $a\neq0$, constants $u_0,c_P\in\mathbb C$, a sign character index $a_0\in\mathbb Z/2$, an integer $n\ge0$ and $\delta\in\{0,1\}$. The assertion is that there exists $\sigma\in\mathbb R$ such that for every $s$ with $\sigma<\operatorname{Re}s$ the function of $q=(x,y_1,y_2)$ given by $$\chi_{u_0,a_0}\big((y_1y_2)^{-1}\big)\,(y_1y_2)^{2}\cdot\Big(\omega_{P_2}(y_2)|y_2|\cdot\!\int_{\mathbb R}\! W(t)\,e^{2\pi i a t x}\,D.W\!\begin{pmatrix}aty_1/y_2&0\\0&1\end{pmatrix}|t|^{s-\frac12}\,\frac{dt}{t^{2}}\cdot\big((y_1y_2)^{-1}\big)^{\delta}e^{-\pi\left(\frac{1+x^{2}}{y_1^{2}}+\frac{1}{y_2^{2}}\right)}|y_1y_2|\,(-ia)^{n}(-iy_2)^{n}\cdot\tfrac12(\pi a^{2}y_2^{2})^{-\frac{w+n+1}{2}}\Gamma\!\big(\tfrac{w+n+1}{2}\big)\Big)\cdot\frac{y_2^{2}}{|y_1y_2|^{4}},$$ with $w=c_P+P_2.\mathrm{centralExponent}+2s$, where $\chi_{u_0,a_0}(y)=|y|^{u_0}$ times $1$ or $\operatorname{sign}(y)$ according as $a_0=0$ or not, and $\omega_{P_2}=\chi_{P_2.\mathrm{centralExponent},\,P_2.\mathrm{centralSign}}$, is integrable for the product of Lebesgue measure on the $x$- and $y_1$-lines with Lebesgue measure restricted to $y_2\in(0,\infty)$.
--
--   This is the archimedean absolute-convergence input for the unfolded Rankin–Selberg torus pair in the converse-theorem part of the Langlands–Tunnell argument: it licenses, in a right half-plane, the Fubini manipulations of the Iwasawa-coordinate integral attached to the section $\det^{\delta}\times$ (column-harmonic) $\times$ Gaussian after the $\theta$-phase has been absorbed. It is used by the three evaluations of the unfolded torus pair for an even principal parameter with the weight-zero, weight-one and discrete Whittaker profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_colHarmonic_of_mulConvGaussian_sheet.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_colHarmonic_of_mulConvGaussian_sheet
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
        ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * q.1) * D.W (ArchR.diagOne (a * t * q.2.1 / q.2.2)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ)) ^ δ *
              (Real.exp (-(Real.pi * ((1 + q.1 ^ 2) / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) *
              ((|q.2.1 * q.2.2| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (q.2.2 : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
