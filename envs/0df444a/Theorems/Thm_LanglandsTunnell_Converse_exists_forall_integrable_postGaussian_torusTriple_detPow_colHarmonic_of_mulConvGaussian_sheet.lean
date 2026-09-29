-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_detPow_colHarmonic_of_mulConvGaussian_sheet
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_detPow_colHarmonic_of_mulConvGaussian_sheet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/e2e9944b-1bd4-5765-ae79-dfd123cdbfc4
-- title:
--   Integrability of the post-Gaussian torus-triple integrand
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb C$, $b\in\mathbb Z/2$, and a function $W:\mathbb R\to\mathbb C$ continuous on $\{t\neq 0\}$ which satisfies two conditions: for every $t>0$,
--   $$W(t)+(-1)^{b}W(-t)=t\cdot 4\int_{0}^{\infty}\bigl(r^{\nu_1}e^{-\pi r^{2}}\bigr)\bigl((t/r)^{\nu_2}e^{-\pi (t/r)^{2}}\bigr)\frac{dr}{r},$$
--   and $W(-t)=(-1)^{b}W(t)$ for all $t\in\mathbb R$. Fix a real archimedean parameter $P_2$ and a datum $D$ for it, i.e. a Whittaker function $D.W$ on $2\times 2$ real matrices, smooth on $\mathrm{GL}_2$, with $D.W(u(x)g)=\psi(x)D.W(g)$, $D.W(zg)=\omega_{P_2}(z)|z|\,D.W(g)$ for $z\neq 0$ (where $\omega_{P_2}(y)=|y|^{c(P_2)}$ times the sign character attached to $P_2$, $c(P_2)$ being $u_1+u_2$ in the principal case and $2u$ in the discrete case), together with the entire zeta functions, functional equation, finite-order and decay-at-$0$ and $\infty$ data. Fix $a\in\mathbb R$, $a\neq 0$, constants $u_0,c_P\in\mathbb C$, $a_0\in\mathbb Z/2$, $n\in\mathbb N$, and $\delta\in\{0,1\}$. Then there is $\sigma\in\mathbb R$ such that for every $s$ with $\operatorname{Re}s>\sigma$ the function of $(t,y_1,y_2)$ given by
--   $$\Bigl[\chi_{u_0,a_0}\bigl((y_1y_2)^{-1}\bigr)\,\bigl(|(y_1y_2)^{-1}|^{2}\bigr)^{-1}\,\omega_{P_2}(y_2)|y_2|\,(y_1y_2)^{-\delta}|y_1y_2|\,(-ia)^{n}(-iy_2)^{n}\tfrac12\bigl(\pi a^{2}y_2^{2}\bigr)^{-\frac{c_P+c(P_2)+2s+n+1}{2}}\Gamma\Bigl(\tfrac{c_P+c(P_2)+2s+n+1}{2}\Bigr)\frac{y_2^{2}}{|y_1y_2|^{4}}\Bigr]\cdot e^{-\pi(y_1^{-2}+y_2^{-2})}|y_1|\cdot W(t)\,D.W\!\begin{pmatrix}aty_1/y_2&0\\0&1\end{pmatrix}|t|^{s-1/2}\,t^{-2}\,e^{-\pi a^{2}t^{2}y_1^{2}}$$
--   (with $\chi_{u_0,a_0}(y)=|y|^{u_0}$, multiplied by $\operatorname{sign}(y)$ when $a_0\neq 0$) is integrable for the product of Lebesgue measure in $t$, Lebesgue measure in $y_1$ and Lebesgue measure restricted to $(0,\infty)$ in $y_2$.
--
--   This is the absolute-convergence statement for the archimedean Rankin–Selberg torus integral attached to the section $\det^{\delta}(M_{02}-iM_{12})^{n}G$, after the inner Gaussian $x$-moment $\int e^{-\pi x^{2}/y_1^{2}}\psi(atxy)\,dx=|y_1|e^{-\pi a^{2}t^{2}y_1^{2}}$ has been carried out, for a $W$ whose $b$-parity part is a multiplicative convolution of two power-times-Gaussian factors. It licenses the interchange of the $(t,y_1,y_2)$ integrations and the fold over sign quadrants in the three evaluations of the unfolded torus pair for the even principal type, in the weight-zero, weight-one and discrete profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_detPow_colHarmonic_of_mulConvGaussian_sheet.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_detPow_colHarmonic_of_mulConvGaussian_sheet
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
        (ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          ((((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ) ^ δ * ((|q.2.1 * q.2.2| : ℝ) : ℂ) *
            (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (q.2.2 : ℂ)) ^ n *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ)))))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
