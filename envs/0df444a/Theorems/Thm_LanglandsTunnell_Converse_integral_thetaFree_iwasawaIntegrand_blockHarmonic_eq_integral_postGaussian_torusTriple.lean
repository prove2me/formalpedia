-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_blockHarmonic_eq_integral_postGaussian_torusTriple
-- name    : LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_blockHarmonic_eq_integral_postGaussian_torusTriple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/6baad468-6664-5bda-9a4c-5a642c36e78a
-- title:
--   Gaussian x-moment step for the block-harmonic Iwasawa integrand
-- statement:
--   Fix complex numbers $\nu_1,\nu_2$, classes $a_1,a_2\in\mathbb Z/2$ and a function $W:\mathbb R\to\mathbb C$ that is continuous on $\{t\neq 0\}$ and satisfies, for each $b\in\mathbb Z/2$ and each $t>0$, the weight-one Gaussian-convolution identity $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_0^{\infty}r^{\nu_1+\delta(a_1+b)}e^{-\pi r^2}(t/r)^{\nu_2+\delta(a_2+b)}e^{-\pi (t/r)^2}\,\frac{dr}{r}$, where $\delta(a)=0$ for $a=0$ and $\delta(a)=1$ otherwise. Let $P_2$ be a real archimedean parameter, $D$ an archimedean Whittaker datum for $P_2$ (a function $D.W$ on real $2\times2$ matrices, smooth on the invertible locus, with the unipotent law against $\psi(x)=e^{2\pi i x}$, the central law against the central character of $P_2$, and entire zeta functions with functional equation, growth and decay conditions), let $a\neq0$ be real, and let $u_0,c_P\in\mathbb C$, $a_0\in\mathbb Z/2$. The assertion is that there is a real $\sigma$ such that for every $s$ with $\operatorname{Re}s>\sigma$, every $y_1\neq 0$ and every $y_2>0$ the following two integrals agree. Write $Q=|(y_1y_2)^{-1}|^{u_0}\varepsilon_{a_0}(y_1y_2)^{-1}\cdot|y_1y_2|^{2}$ (with $\varepsilon_{a_0}$ trivial if $a_0=0$ and the sign character otherwise), $C=\chi_{P_2}(y_2)|y_2|$ with $\chi_{P_2}$ the central character of $P_2$, $w=c_P+P_2.\mathrm{centralExponent}+2s+2$ and $R=|y_1y_2|\,(-ia)(-iy_2)\cdot\tfrac12(\pi a^2y_2^2)^{-w/2}\Gamma(w/2)\cdot y_2^2|y_1y_2|^{-4}$. The left-hand side is the integral over $x\in\mathbb R$ of
--   $$Q\,C\Bigl(\int_{\mathbb R}W(t)\,e^{2\pi i a t x}\,D.W\bigl(\mathrm{diag}(aty_1/y_2,1)\bigr)|t|^{s-1/2}t^{-2}\,dt\Bigr)\Bigl(\tfrac1{y_1}+\tfrac1{y_2}+\tfrac{ix}{y_1}\Bigr)e^{-\pi\bigl(\frac{1+x^2}{y_1^2}+\frac1{y_2^2}\bigr)}R,$$
--   and the right-hand side is the integral over $t\in\mathbb R$ of
--   $$Q\,C\,R\;e^{-\pi(1/y_1^2+1/y_2^2)}|y_1|\;W(t)\,D.W\bigl(\mathrm{diag}(aty_1/y_2,1)\bigr)|t|^{s-1/2}t^{-2}\,e^{-\pi a^2t^2y_1^2}\Bigl(\tfrac1{y_1}+\tfrac1{y_2}-aty_1\Bigr),$$
--   the scalar factors being grouped exactly as indicated.
--
--   This is the $x$-integration step in the archimedean unfolding computation behind the converse-theorem input: the order of the $x$- and $t$-integrations is exchanged and the resulting Gaussian moment $\int_{\mathbb R}e^{-\pi x^2/y_1^2}(\frac1{y_1}+\frac1{y_2}+\frac{ix}{y_1})e^{2\pi i atx}\,dx=|y_1|e^{-\pi a^2t^2y_1^2}(\frac1{y_1}+\frac1{y_2}-aty_1)$ is evaluated, turning the $\theta$-free block-harmonic Iwasawa integrand into the post-Gaussian torus-triple integrand. It feeds the weight-one assembly of the unfolded torus pair with its explicit gamma factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_blockHarmonic_eq_integral_postGaussian_torusTriple.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_blockHarmonic_eq_integral_postGaussian_torusTriple
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      (∫ x : ℝ,
        ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ + 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ + 1 / y₂ - a * t * y₁ : ℝ)) : ℂ)))) := by sorry
