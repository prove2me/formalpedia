-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_blockHarmonic_of_mulConvGaussian_sheets
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_blockHarmonic_of_mulConvGaussian_sheets
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/b9ad70e9-f397-5192-b3db-cba5251dd9b8
-- title:
--   Integrability of the θ-free block-harmonic Iwasawa integrand
-- statement:
--   Let $\nu_1,\nu_2\in\mathbb{C}$ and $a_1,a_2\in\mathbb{Z}/2$, and let $W:\mathbb{R}\to\mathbb{C}$ be continuous on $\{t\neq 0\}$ and satisfy, for every $b\in\mathbb{Z}/2$ and every $t>0$, the two-sheet Gaussian-convolution identity $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_{0}^{\infty}r^{\nu_1+\mathrm{signShift}(a_1+b)}e^{-\pi r^{2}}\,(t/r)^{\nu_2+\mathrm{signShift}(a_2+b)}e^{-\pi (t/r)^{2}}\,\frac{dr}{r}$, where $\mathrm{signShift}(c)=0$ for $c=0$ and $1$ otherwise. Let $P_2$ be a real archimedean parameter (principal or discrete), $D$ an `ArchDatumR P₂`, i.e. a real archimedean Whittaker datum: a function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with unipotent law $D.W(n(x)g)=e^{2\pi i x}D.W(g)$, central law governed by $\mathrm{centralChar}\,P_2$, entire zeta functions with functional equation and finite order, and the prescribed torus decay at $\infty$ and at $0$. Let $a\neq0$ be real, $u_0,c_P\in\mathbb{C}$ and $a_0\in\mathbb{Z}/2$. Then there is $\sigma\in\mathbb{R}$ such that for every $s$ with $\operatorname{Re}s>\sigma$ the function of $(x,y_1,y_2)$ given by $$\chi_{u_0,a_0}\bigl((y_1y_2)^{-1}\bigr)\,|y_1y_2|^{2}\Bigl(\chi_{P_2}(y_2)|y_2|\int_{\mathbb{R}}W(t)\,e^{2\pi i a t x}\,D.W\!\begin{pmatrix}aty_1/y_2&0\\0&1\end{pmatrix}|t|^{s-1/2}t^{-2}\,dt\Bigr)\cdot\Bigl(\tfrac1{y_1}+\tfrac1{y_2}+\tfrac{ix}{y_1}\Bigr)e^{-\pi\left(\frac{1+x^{2}}{y_1^{2}}+\frac1{y_2^{2}}\right)}|y_1y_2|\,(-ia)(-iy_2)\,\tfrac12(\pi a^{2}y_2^{2})^{-w/2}\Gamma(w/2)\cdot y_2^{2}|y_1y_2|^{-4},$$ with $w=c_P+P_2.\mathrm{centralExponent}+2s+2$, $\chi_{u_0,a_0}(y)=|y|^{u_0}$ times $\mathrm{sign}(y)$ when $a_0\neq0$, and $\chi_{P_2}=\mathrm{centralChar}\,P_2$, is integrable for the product of Lebesgue measure in $x$, Lebesgue measure in $y_1$, and Lebesgue measure restricted to $(0,\infty)$ in $y_2$.
--
--   This is the absolute-convergence input that legitimises interchanging the inner $t$-integral with the integration in Iwasawa coordinates $(x,y_1,y_2)$ for the unfolded torus pair in the major, block-harmonic section of the Rankin–Selberg computation, with the theta sum already removed. It is used by the evaluation of the unfolded torus pair in closed form as an explicit expression times an archimedean gamma factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_blockHarmonic_of_mulConvGaussian_sheets.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_blockHarmonic_of_mulConvGaussian_sheets
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
        ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * q.1) * D.W (ArchR.diagOne (a * t * q.2.1 / q.2.2)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / q.2.1 + 1 / q.2.2 : ℝ) : ℂ)) + Complex.I * (((q.1 / q.2.1 : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + q.1 ^ 2) / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) *
              ((|q.2.1 * q.2.2| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) * (-Complex.I * (q.2.2 : ℂ)) *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
