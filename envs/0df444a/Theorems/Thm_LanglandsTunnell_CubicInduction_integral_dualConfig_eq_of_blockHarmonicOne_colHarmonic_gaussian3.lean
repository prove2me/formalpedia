-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_blockHarmonicOne_colHarmonic_gaussian3
-- name    : LanglandsTunnell.CubicInduction.integral_dualConfig_eq_of_blockHarmonicOne_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/054e5336-c0d3-5fc7-971c-6ec0f7ac8b76
-- title:
--   Dual-configuration Godement integral of a harmonic Gaussian section
-- statement:
--   Let $a$ be a non-zero rational number and let $\psi_\infty$ be an additive character of the infinite adele ring of $\mathbb{Q}$ satisfying $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$ for all $x$, where [`NumberField.StandardAddChar.psiArch`](def/NumberField_StandardGlobalAddCharRat.html#L556) is the character sending $x$ to the finite product over the infinite places $v$ of $\exp(2\pi i\,\iota_v(x_v))$, $\iota_v$ the real embedding of the completion at $v$. Let $n$ be a natural number and let $S$ be the function on real $2\times 3$ matrices given by $S(M)=\bigl((M_{00}+iM_{10})-i(M_{01}+iM_{11})\bigr)\,(M_{02}-iM_{12})^{n}\,\exp\bigl(-\pi\sum_{i,b}M_{ib}^{2}\bigr)$, the last factor being `gaussian3`. Let $e$ be a $2\times2$ real array with $\det e\neq0$, and let $a_1,a_2$ be non-zero reals. Writing $\rho_j=(e^{-1})_{1j}$ for the entries of the second row of $e^{-1}$, and with the character evaluated on the infinite adele all of whose real components equal $-v_1$ (the map [`AutomorphicForm.StandardKernel.ofReal`](def/AutomorphicForm_SmoothingKernel.html#L774)), the assertion is $$\int_{\mathbb{R}^2}S\Bigl(e\cdot\begin{pmatrix}v_0/a_1&0&1\\ v_1/a_1&a_2^{-1}&0\end{pmatrix}\Bigr)\psi_\infty(-v_1)\,dv=(e_{00}-ie_{10})^{n}e^{-\pi\left(a_2^{-2}(e_{01}^2+e_{11}^2)+e_{00}^2+e_{10}^2\right)}\frac{a_1^{2}}{|\det e|}\cdot(-i)\bigl[a a_1(\rho_0+i\rho_1)+a_2^{-1}(e_{01}+ie_{11})\bigr]e^{-\pi a^{2}a_1^{2}(\rho_0^2+\rho_1^2)},$$ the Lebesgue integral being taken over $v\in\mathbb{R}^2$.
--
--   This is the closed evaluation of the archimedean inner integral occurring in the dual configuration of the Godement-type unfolding, for the section built from one block-harmonic linear factor, a column-harmonic factor of degree $n$ and the standard Gaussian; it is obtained from the Fourier transform of a harmonic polynomial times a Gaussian on $\mathbb{R}^2$ (`integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two`) after the substitution $u=a_1^{-1}ev$. It feeds the identification of the dual torus pair integral in the Rankin–Selberg step, [`LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_blockHarmonicOne_colHarmonic_gaussian3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction MeasureTheory

theorem LanglandsTunnell.CubicInduction.integral_dualConfig_eq_of_blockHarmonicOne_colHarmonic_gaussian3
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (n : ℕ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ))) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : a₂ ≠ 0) :
    (∫ v : Fin 2 → ℝ,
        S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
          psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))))
      = (((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ n *
          (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
          (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
          (-Complex.I *
            ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
              (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ)))) *
          (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ) := by sorry
