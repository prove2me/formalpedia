-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_eq_integral_postGaussian_torusTriple
-- name    : LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_eq_integral_postGaussian_torusTriple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/86e852b4-daaa-5c65-b2ea-4ad3e55a647c
-- title:
--   x-integration of the quadratic θ-free Iwasawa integrand
-- statement:
--   Fix $\nu_1,\nu_2\in\mathbb{C}$, a parity $b\in\mathbb{Z}/2$ and a function $W:\mathbb{R}\to\mathbb{C}$ continuous on $\{t\neq 0\}$ which satisfies the one-sheet multiplicative-convolution identity $W(t)+(-1)^{b}W(-t)=t\cdot 4\int_{0}^{\infty} r^{\nu_1}e^{-\pi r^{2}}\,(t/r)^{\nu_2}e^{-\pi (t/r)^{2}}\,\frac{dr}{r}$ for $t>0$, together with the parity law $W(-t)=(-1)^{b}W(t)$ for all $t$. Fix a real archimedean parameter $P_2$ (principal or discrete series data) and an archimedean Whittaker datum $D$ for $P_2$, i.e. a function $D.W$ on real $2\times 2$ matrices, smooth on the invertible locus, with $D.W(n(x)g)=e^{2\pi i x}D.W(g)$, the central law for $P_2$, entire zeta functions with the prescribed functional equation, finite order and the stated decay bounds. Fix $a\in\mathbb{R}$, $a\neq 0$, constants $u_0,c_P\in\mathbb{C}$, $a_0\in\mathbb{Z}/2$, and $\delta\in\{0,1\}$. The assertion is that there is $\sigma\in\mathbb{R}$ such that for every $s$ with $\operatorname{Re}s>\sigma$, every $y_1\neq 0$ and every $y_2>0$ the integral over $x\in\mathbb{R}$ of the $\theta$-free quadratic Iwasawa integrand equals the corresponding integral over $t\in\mathbb{R}$. Both sides carry the same $x$- and $t$-free factors, namely $\mathrm{quasiChar}(u_0,a_0)\big((y_1y_2)^{-1}\big)=|(y_1y_2)^{-1}|^{u_0}$ times the sign $\operatorname{sign}((y_1y_2)^{-1})$ when $a_0\neq 0$, the factor $(|(y_1y_2)^{-1}|^{2})^{-1}$, the central character value $\mathrm{centralChar}(P_2,y_2)\,|y_2|$ attached to the central exponent and sign of $P_2$, the factors $((y_1y_2)^{-1})^{\delta}$, $|y_1y_2|$, $(-ia)^{2}$, $(-iy_2)^{2}$, the gamma factor $\tfrac12(\pi a^{2}y_2^{2})^{-(c_P+\mathrm{centralExponent}(P_2)+2s+3)/2}\,\Gamma\big((c_P+\mathrm{centralExponent}(P_2)+2s+3)/2\big)$, and $y_2^{2}|y_1y_2|^{-4}$. On the left the remaining $x$-dependent part is the inner integral $\int_{\mathbb{R}}W(t)\,e^{2\pi i\,atx}\,D.W(\mathrm{diag}(at y_1/y_2,1))\,|t|^{s-1/2}t^{-2}\,dt$ multiplied by $\big((1+x^{2})/y_1^{2}-1/y_2^{2}-2ix/(y_1y_2)\big)e^{-\pi((1+x^{2})/y_1^{2}+1/y_2^{2})}$; on the right it is replaced by $e^{-\pi(1/y_1^{2}+1/y_2^{2})}|y_1|$ times $W(t)\,D.W(\mathrm{diag}(at y_1/y_2,1))\,|t|^{s-1/2}t^{-2}\,e^{-\pi a^{2}t^{2}y_1^{2}}\big(1/y_1^{2}-1/y_2^{2}-a^{2}t^{2}y_1^{2}+1/(2\pi)+2at y_1/y_2\big)$, integrated in $t$.
--
--   This is the $x$-integration step in the unfolding of the Rankin–Selberg integral attached to the quadratic (degree-two column-harmonic) section of the archimedean converse theorem: the Gaussian moments of orders $0,1,2$ in $x$ are evaluated and the order of integration in $x$ and $t$ is exchanged, producing the post-Gaussian torus-triple integrand with the bracket $1/y_1^{2}-1/y_2^{2}-a^{2}t^{2}y_1^{2}+1/(2\pi)+2at y_1/y_2$. It feeds the explicit evaluation of the unfolded torus-pair integral as an elementary expression times a gamma factor for even principal-series data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_eq_integral_postGaussian_torusTriple.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_eq_integral_postGaussian_torusTriple
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
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      (∫ x : ℝ,
        ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
              ((((1 + x ^ 2) / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ)))) := by sorry
