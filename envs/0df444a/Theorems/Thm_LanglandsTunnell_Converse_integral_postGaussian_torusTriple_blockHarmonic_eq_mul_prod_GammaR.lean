-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_postGaussian_torusTriple_blockHarmonic_eq_mul_prod_GammaR
-- name    : LanglandsTunnell.Converse.integral_postGaussian_torusTriple_blockHarmonic_eq_mul_prod_GammaR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/678edeaf-cc1f-5f34-8ba5-5ab9145307e3
-- title:
--   Evaluation of the post-Gaussian block-harmonic torus-triple integral
-- statement:
--   Write $G_{p,q}(y)=4\int_0^\infty r^{p}e^{-\pi r^{2}}\,(y/r)^{q}e^{-\pi (y/r)^{2}}\,dr/r$ and $[\,a\,]=$ `signShift` $a$, i.e. $0$ if $a=0$ and $1$ otherwise. Fix $\nu_1,\nu_2\in\mathbb C$, classes $a_1,a_2,c\in\mathbb Z/2$ with $a_1\neq a_2$, and $W:\mathbb R\to\mathbb C$ continuous on $\{t\neq 0\}$ such that for both $b\in\mathbb Z/2$ and all $t>0$ one has $W(t)+(-1)^{b}W(-t)=t\,G_{\nu_1+[a_1+b],\,\nu_2+[a_2+b]}(t)$. Fix $\mu_1,\mu_2\in\mathbb C$ and an archimedean datum $D$ of type `ArchDatumR` for a real parameter $P_2$ equal to $\mathrm{principal}(\mu_1,c,\mu_2,c)$ (so $D.W$ is smooth on the invertible matrices, transforms by $\psi$ under unipotents and by $\mathrm{centralChar}\,P_2$ under the centre, and carries entire zeta functions with functional equation, finite order and the decay bounds required by the structure); assume $D.W(\mathrm{diag}(\tau,1))=\rho\,\tau\,G_{\mu_1,\mu_2}(\tau)$ and $D.W(\mathrm{diag}(-\tau,1))=(-1)^{c}D.W(\mathrm{diag}(\tau,1))$ for all $\tau>0$, for some $\rho\in\mathbb C$. Finally let $a=-1$, let $u_0\in\mathbb C$, let $c_P=\nu_1+\nu_2$ and $a_0=c$. Then there is $\sigma\in\mathbb R$ such that for every $s$ with $\operatorname{Re}s>\sigma$ the integral over $(t,y_1,y_2)\in\mathbb R\times\mathbb R\times(0,\infty)$ (Lebesgue measure on the first two factors, Lebesgue measure restricted to $(0,\infty)$ on the third) of the displayed integrand — the product of $\mathrm{quasiChar}(u_0+2,a_0)\bigl((y_1y_2)^{-1}\bigr)=|y_1y_2|^{-(u_0+2)}$ times the sign factor for $a_0$, of $\bigl(|(y_1y_2)^{-1}|^{2}\bigr)^{-1}$, of $\mathrm{centralChar}(P_2,y_2)\,|y_2|$, of $|y_1y_2|\,(-ia)(-iy_2)$, of the Gaussian Mellin factor $\tfrac12(\pi a^{2}y_2^{2})^{-w/2}\Gamma(w/2)$ with $w=c_P+\mu_1+\mu_2+2s+2$, of $y_2^{2}|y_1y_2|^{-4}$, of $e^{-\pi(1/y_1^{2}+1/y_2^{2})}|y_1|$, and of $W(t)\,D.W(\mathrm{diag}(a t y_1/y_2,1))\,|t|^{s-1/2}t^{-2}e^{-\pi a^{2}t^{2}y_1^{2}}\bigl(1/y_1+1/y_2-a t y_1\bigr)$ — equals
--   $$(-1)^{c}\,\rho\,\tfrac12\prod_{i=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12+\nu_i+u_0+[a_i+c]\bigr)\prod_{i,j=1,2}\Gamma_{\mathbb R}\bigl(s+\tfrac12+\nu_i+\mu_j+[a_i+c]\bigr),$$
--   where $\Gamma_{\mathbb R}(z)=\pi^{-z/2}\Gamma(z/2)$, the six factors occurring in the order $(u_0;\mu_1;\mu_2)$ for $i=1,2$.
--
--   This is the archimedean evaluation step in the Rankin–Selberg computation attached to the converse theorem used in the Langlands–Tunnell argument: after the Iwasawa unfolding and the Gaussian integration in the $x$-variable, the remaining triple integral over a torus pair is computed in closed form as a product of six $\Gamma_{\mathbb R}$-factors, the shape expected for the archimedean factor of a $\mathrm{GL}_2\times\mathrm{GL}_2$ convolution of a weight-one vector with a principal-series datum. It feeds the assembly [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3_of_profile), and relies on a quadrant fold of the plane integral, the two Whittaker profiles, and a Barnes-type triple-integral evaluation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_postGaussian_torusTriple_blockHarmonic_eq_mul_prod_GammaR.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.integral_postGaussian_torusTriple_blockHarmonic_eq_mul_prod_GammaR
    (ν₁ ν₂ : ℂ) (a₁ a₂ c : ZMod 2) (h12 : a₁ ≠ a₂)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ : ZMod 2) (ha₀ : a₀ = c) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      ∫ q : ℝ × ℝ × ℝ,
        (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          (((|q.2.1 * q.2.2| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * (-Complex.I * (q.2.2 : ℂ)) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (((1 / q.2.1 + 1 / q.2.2 - a * q.1 * q.2.1 : ℝ)) : ℂ))))
        ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) =
      (-1 : ℂ) ^ c.val * ρ * (1 / 2 : ℂ) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + u₀) + signShift (a₁ + c))) *
          Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + u₀) + signShift (a₂ + c)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₁) + signShift (a₁ + c))) *
            Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₁) + signShift (a₂ + c)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₂) + signShift (a₁ + c))) *
              Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₂) + signShift (a₂ + c)))))) := by sorry
