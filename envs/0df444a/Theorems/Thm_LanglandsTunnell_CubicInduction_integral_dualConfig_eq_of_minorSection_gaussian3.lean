-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_minorSection_gaussian3
-- name    : LanglandsTunnell.CubicInduction.integral_dualConfig_eq_of_minorSection_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/e17f8413-1d22-53d7-8cc0-7292e6b9af38
-- title:
--   Dual-configuration integral of the minor Gaussian section
-- statement:
--   Let $a$ be a non-zero rational, and let $\psi_\infty$ be an additive character of the infinite adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$ which is assumed to satisfy $\psi_\infty(x) = \psi_{\mathrm{arch}}(a x)$ for all $x$, where $\psi_{\mathrm{arch}}$ is the standard archimedean character, the finite product over the infinite places $v$ of $x \mapsto \exp(2\pi i\, x_v)$ under the identification of $\mathbb{Q}_v$ with $\mathbb{R}$. Let $S : \mathrm{Mat}_{2\times 3}(\mathbb{R}) \to \mathbb{C}$ be the function $S(M) = \bigl((M_{00} - iM_{01})M_{12} - (M_{10} - iM_{11})M_{02}\bigr)\,\mathrm{gaussian3}(M)$, with $\mathrm{gaussian3}(M) = \exp\bigl(-\pi\sum_{i<2}\sum_{b<3} M_{ib}^2\bigr)$. Let $e$ be a $2\times 2$ real array with $\det e \neq 0$, and let $a_1, a_2$ be non-zero reals. Writing $\rho = ((e^{-1})_{10}, (e^{-1})_{11})$ for the second row of $e^{-1}$, the assertion is the equality of Bochner integrals over $\mathbb{R}^2$ $$\int S\Bigl(e\cdot\begin{pmatrix} v_0/a_1 & 0 & 1\\ v_1/a_1 & a_2^{-1} & 0\end{pmatrix}\Bigr)\,\psi_\infty\bigl(\iota(-v_1)\bigr)\,dv = e^{-\pi\left(a_2^{-2}(e_{01}^2+e_{11}^2)+(e_{00}^2+e_{10}^2)\right)}\cdot\frac{a_1^2}{|\det e|}\cdot\Bigl(-i\,a\,a_1\bigl(\rho_0 e_{10} - \rho_1 e_{00}\bigr) + i\,a_2^{-1}\det e\Bigr)\cdot e^{-\pi a^2 a_1^2(\rho_0^2+\rho_1^2)},$$ where $\iota(r)$ denotes the infinite adele all of whose components are $r$ under the real identifications. Only the value of the integral is asserted, not integrability of the integrand.
--
--   This is the closed-form evaluation of the archimedean inner (Godement) integral attached to the minor Schwartz section $S$ of the $2\times 3$ Gaussian family, taken in the dual configuration in which the two $v$-independent columns of the matrix argument are $a_2^{-1}e_{\cdot 1}$ and $e_{\cdot 0}$. It is used in the unfolding computation [`LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_minorSection_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_minorSection_gaussian3), and is the dual companion of the corresponding primal evaluations; the Fourier transform input is the Gaussian harmonic-polynomial integral [`LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two`](thm.html#LanglandsTunnell.CubicInduction.integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_minorSection_gaussian3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction MeasureTheory

theorem LanglandsTunnell.CubicInduction.integral_dualConfig_eq_of_minorSection_gaussian3
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 0 1 : ℝ) : ℂ)) * ((M 1 2 : ℝ) : ℂ) -
        (((M 1 0 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ)) * ((M 0 2 : ℝ) : ℂ)) * gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : a₂ ≠ 0) :
    (∫ v : Fin 2 → ℝ,
        S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
          psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))))
      = (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
          (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
          (-Complex.I * (a : ℂ) * (a₁ : ℂ) *
              ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) * ((e 1 0 : ℝ) : ℂ) - (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ) * ((e 0 0 : ℝ) : ℂ)) +
            Complex.I * (a₂⁻¹ : ℂ) * (((Matrix.of e).det : ℝ) : ℂ)) *
          (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ) := by sorry
