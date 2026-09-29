-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/9ab5c4de-6f44-5978-a87c-5a64ac056330
-- title:
--   Integrability of the post-Gaussian torus-triple integrand, quadratic section
-- statement:
--   Fix complex numbers $\nu_1,\nu_2$, a class $b\in\mathbb Z/2$, and a function $W:\mathbb R\to\mathbb C$ that is continuous on $\{t\in\mathbb R: t\neq 0\}$, satisfies the parity rule $W(-t)=(-1)^{b}W(t)$ for all $t$, and satisfies, for every $t>0$, $$W(t)+(-1)^{b}W(-t)=4t\int_0^\infty r^{\nu_1}e^{-\pi r^{2}}\,(t/r)^{\nu_2}e^{-\pi (t/r)^{2}}\,\frac{dr}{r}.$$ Fix further a real archimedean parameter $P_2$ and an archimedean datum $D$ for it, i.e. a function $D.W$ on real $2\times2$ matrices, smooth on the invertible locus, with $D.W(n(x)g)=\psi(x)D.W(g)$ and $D.W(zg)=\mathrm{centralChar}_{P_2}(z)\,|z|\,D.W(g)$ for $z\neq0$, whose zeta integrals converge in a right half plane and equal the archimedean factor of the twisted parameter times an entire function of finite order satisfying the expected functional equation, with the prescribed decay of all derivatives along $\mathrm{diag}(y,1)k$ as $|y|\to\infty$ and as $|y|\to 0$; a real $a\neq0$; complex numbers $u_0,c_P$; a class $a_0\in\mathbb Z/2$; and $\delta\in\{0,1\}$. Then there exists $\sigma\in\mathbb R$ such that for every $s$ with $\mathrm{Re}\,s>\sigma$ the function of $(t,y_1,y_2)$ equal to the product of $$\bigl|(y_1y_2)^{-1}\bigr|^{u_0}\varepsilon_{a_0}\bigl(\mathrm{sign}\,(y_1y_2)^{-1}\bigr)\cdot|y_1y_2|^{2}\cdot\bigl(|y_2|^{c(P_2)}\varepsilon_{P_2}(\mathrm{sign}\,y_2)\,|y_2|\bigr)\cdot(y_1y_2)^{-\delta}|y_1y_2|\,(-ia)^{2}(-iy_2)^{2}\cdot\tfrac12(\pi a^{2}y_2^{2})^{-w}\Gamma(w)\cdot y_2^{2}|y_1y_2|^{-4},$$ where $w=(c_P+c(P_2)+2s+2+1)/2$ and $c(P_2)$ is the central exponent of $P_2$ (so $u_1+u_2$ in the principal case, $2u$ in the discrete case) and $\varepsilon_\bullet$ is the factor $1$ or $\mathrm{sign}$ according as the relevant class in $\mathbb Z/2$ vanishes or not, with $$e^{-\pi(1/y_1^{2}+1/y_2^{2})}|y_1|\cdot W(t)\,D.W\bigl(\mathrm{diag}(at y_1/y_2,\,1)\bigr)\,|t|^{s-1/2}\,t^{-2}\,e^{-\pi a^{2}t^{2}y_1^{2}}\Bigl(\tfrac1{y_1^{2}}-\tfrac1{y_2^{2}}-a^{2}t^{2}y_1^{2}+\tfrac1{2\pi}+\tfrac{2aty_1}{y_2}\Bigr)$$ is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$ for Lebesgue measure in each variable, the last factor being restricted to $(0,\infty)$.
--
--   This is the convergence statement that licenses the interchange of integrations in the $(t,y_1,y_2)$ evaluation of the quadratic section of the torus-triple integral occurring in the converse-theorem computation: the integrand is the one obtained after the $x$-integration has produced the Gaussian and Gamma factors together with the polynomial bracket $1/y_1^2-1/y_2^2-a^2t^2y_1^2+1/(2\pi)+2aty_1/y_2$. It is used by the theorem evaluating that integral as an explicit multiple of a product of real Gamma factors, and by the corresponding Rankin–Selberg unfolding statement in the even principal-series case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
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
        (ArchR.quasiChar u₀ a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          ((((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ) ^ δ * ((|q.2.1 * q.2.2| : ℝ) : ℂ) *
            (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (q.2.2 : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (((1 / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 - a ^ 2 * q.1 ^ 2 * q.2.1 ^ 2 + 1 / (2 * Real.pi) + 2 * a * q.1 * q.2.1 / q.2.2 : ℝ)) : ℂ)))))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
