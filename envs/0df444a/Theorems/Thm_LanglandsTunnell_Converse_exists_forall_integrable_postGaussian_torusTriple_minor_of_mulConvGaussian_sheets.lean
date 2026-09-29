-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_minor_of_mulConvGaussian_sheets
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_minor_of_mulConvGaussian_sheets
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/7d0712b6-01a1-5a0f-af78-57b585d28f6a
-- title:
--   Integrability of the post-Gaussian minor-section torus triple integrand
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb C$ and $a_1,a_2\in\mathbb Z/2$, and let $W:\mathbb R\to\mathbb C$ be continuous on $\{t\neq 0\}$ and satisfy, for every $b\in\mathbb Z/2$ and every $t>0$, the two-sheet Gaussian-convolution identity $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_{0}^{\infty} r^{\nu_1+\mathrm{sh}(a_1+b)}e^{-\pi r^{2}}\,(t/r)^{\nu_2+\mathrm{sh}(a_2+b)}e^{-\pi (t/r)^{2}}\,\frac{dr}{r}$, where $\mathrm{sh}(a)=0$ for $a=0$ and $1$ otherwise. Let $P_2$ be a real archimedean parameter, $D$ a real archimedean Whittaker datum for $P_2$ (a function $D.W$ on $2\times 2$ real matrices, smooth on the invertible locus, with the unipotent and central transformation laws and the entirety, functional-equation, growth and decay properties packaged in `ArchDatumR`), $a\in\mathbb R$ with $a\neq 0$, $u_0,c_P\in\mathbb C$ and $a_0\in\mathbb Z/2$. Then there is $\sigma\in\mathbb R$ such that for every $s$ with $\operatorname{Re} s>\sigma$ and all $b_0,b_1\in\mathbb C$ the function of $(t,y_1,y_2)$ given by the product of the $t$-free prefactor $$\chi_{u_0,a_0}\big((y_1y_2)^{-1}\big)\,|y_1y_2|^{2}\cdot\big(\chi_{P_2}(y_2)|y_2|\big)\cdot |y_1y_2|\,(-ia)\,\frac{y_2}{y_1}\cdot\tfrac12(\pi a^{2}y_2^{2})^{-w/2}\Gamma(w/2)\cdot y_2^{2}|y_1y_2|^{-4},\qquad w=c_P+P_2.\mathrm{centralExponent}+2s+2,$$ with $\chi_{u,\alpha}(y)=|y|^{u}$ times $\operatorname{sign}(y)$ when $\alpha\neq 0$ and $\chi_{P_2}=\chi_{P_2.\mathrm{centralExponent},\,P_2.\mathrm{centralSign}}$, by $e^{-\pi(1/y_1^{2}+1/y_2^{2})}|y_1|$, and by $$W(t)\,D.W\!\left(\begin{smallmatrix} a t y_1/y_2&0\\0&1\end{smallmatrix}\right)|t|^{s-1/2}t^{-2}e^{-\pi (at)^{2}y_1^{2}}\big(b_0-b_1\,(at)y_1^{2}\big)$$ is integrable on $\mathbb R\times\mathbb R\times\mathbb R$ for Lebesgue measure in $t$ and $y_1$ and Lebesgue measure restricted to $(0,\infty)$ in $y_2$. The abscissa $\sigma$ is uniform in $b_0,b_1$, so the two terms of the affine bracket are covered separately.
--
--   This is the absolute-convergence input for the torus-triple stage of the Rankin–Selberg computation attached to the converse theorem in the Langlands–Tunnell argument: it licenses interchanging the $t$-, $y_1$- and $y_2$-integrations after the Gaussian moment in $x$ has been evaluated, together with the subsequent sign folds and the splitting of the affine bracket into its two terms. It is used in the evaluation of the unfolded minor-section torus pair for a weight-one profile.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_minor_of_mulConvGaussian_sheets.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_minor_of_mulConvGaussian_sheets
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ b₀ b₁ : ℂ,
      Integrable (fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          (((|q.2.1 * q.2.2| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * ((q.2.2 / q.2.1 : ℝ) : ℂ) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (b₀ - b₁ * (((a * q.1) * q.2.1 ^ 2 : ℝ) : ℂ))))))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
