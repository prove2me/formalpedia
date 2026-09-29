-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple
-- name    : LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/a0249410-49b0-5c50-9243-b3e5e3812b1f
-- title:
--   Gaussian x-integration of the conjugate-block Iwasawa integrand
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb C$, $a_1,a_2\in\mathbb Z/2$ and $W:\mathbb R\to\mathbb C$ continuous on $\{t\neq 0\}$ and satisfying, for every $b\in\mathbb Z/2$ and every $t>0$, the Gaussian-convolution profile identity $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_0^\infty r^{\nu_1+\sigma(a_1+b)}e^{-\pi r^2}(t/r)^{\nu_2+\sigma(a_2+b)}e^{-\pi (t/r)^2}\,dr/r$, where $\sigma(a)=0$ for $a=0$ and $\sigma(a)=1$ otherwise. Let $P_2$ be a real archimedean parameter, $D$ an archimedean Whittaker datum for $P_2$ (a function $D.W$ on real $2\times2$ matrices with the unipotent law for $\psi(x)=e^{2\pi i x}$, the central law for the central quasicharacter of $P_2$, and the stated smoothness, zeta-integral and decay properties), $a\neq 0$ real, $u_0,c_P\in\mathbb C$, $a_0\in\mathbb Z/2$ and $n\in\mathbb N$. Then there is $\sigma_0\in\mathbb R$ such that for all $s$ with $\operatorname{Re}s>\sigma_0$, all $y_1\neq0$ and all $y_2>0$, writing $Q=\chi_{u_0,a_0}((y_1y_2)^{-1})\,|(y_1y_2)^{-1}|^{-2}$ with $\chi_{u,a}(y)=|y|^{u}(\operatorname{sign}y)^{[a\neq0]}$, $w=c_P+c_{P_2}+2s+n+1$ ($c_{P_2}$ the central exponent of $P_2$), and $R=|y_1y_2|\,(-ia)^n(-iy_2)^n\cdot\tfrac12(\pi a^2y_2^2)^{-w/2}\Gamma(w/2)$, one has
--   $$\int_{\mathbb R}Q\,\Bigl(\chi_{P_2}(y_2)|y_2|\int_{\mathbb R}W(t)\psi(atx)\,D.W\!\left(\begin{smallmatrix}aty_1/y_2&0\\0&1\end{smallmatrix}\right)|t|^{s-\frac12}t^{-2}dt\Bigr)\Bigl(\tfrac1{y_1}-\tfrac1{y_2}+\tfrac{ix}{y_1}\Bigr)e^{-\pi\left(\frac{1+x^2}{y_1^2}+\frac1{y_2^2}\right)}R\;y_2^2|y_1y_2|^{-4}\,dx$$
--   equals
--   $$\int_{\mathbb R}Q\,\chi_{P_2}(y_2)|y_2|\,R\,y_2^2|y_1y_2|^{-4}\cdot e^{-\pi\left(\frac1{y_1^2}+\frac1{y_2^2}\right)}|y_1|\cdot W(t)\,D.W\!\left(\begin{smallmatrix}aty_1/y_2&0\\0&1\end{smallmatrix}\right)|t|^{s-\frac12}t^{-2}e^{-\pi a^2t^2y_1^2}\Bigl(\tfrac1{y_1}-\tfrac1{y_2}-aty_1\Bigr)dt,$$
--   the constant factors being grouped exactly as written on each side.
--
--   This is the $x$-integration step in the archimedean computation attached to the unfolded conjugate-block torus pair: the inner $t$-integral is interchanged with the $x$-integral and the resulting Gaussian moments $\int_{\mathbb R}e^{-\pi x^2/y_1^2}(c+ix/y_1)\psi(atx)\,dx=|y_1|e^{-\pi a^2t^2y_1^2}(c-aty_1)$ of orders $0$ and $1$ are evaluated, so that the whole expression becomes a single integral in $t$. It feeds the two evaluations of the unfolded torus pair in weight one as an explicit expression times a gamma factor, for the discrete and weight-one archimedean profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) (n : ℕ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      (∫ x : ℝ,
        ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ - 1 / y₂ - a * t * y₁ : ℝ)) : ℂ)))) := by sorry
