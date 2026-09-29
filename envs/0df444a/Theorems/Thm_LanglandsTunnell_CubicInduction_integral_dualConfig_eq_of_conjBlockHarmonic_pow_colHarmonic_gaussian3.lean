-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- name    : LanglandsTunnell.CubicInduction.integral_dualConfig_eq_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/be68ba6b-783c-5a42-9bb4-206a2593a04d
-- title:
--   Dual-configuration Gaussian integral for the degree-m flat section
-- statement:
--   Fix a non-zero rational $a$ and an additive character $\psi_\infty$ of the infinite adele ring of $\mathbb{Q}$ which is assumed to satisfy $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$ for all $x$, where [`NumberField.StandardAddChar.psiArch`](def/NumberField_StandardGlobalAddCharRat.html#L556) is the character sending $x$ to the finite product over the infinite places $v$ of $\exp(2\pi i\,x_v)$, each $x_v$ read as a real number through the real completion at $v$. Fix natural numbers $n,m$, a sign $\varepsilon'=\pm 1$, and let $S:\mathrm{Mat}_{2\times 3}(\mathbb{R})\to\mathbb{C}$ be the function $$S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m\,(M_{02}+\varepsilon' i M_{12})^n\,e^{-\pi\sum_{i,b}M_{ib}^2},$$ the last factor being `gaussian3`. Let $e$ be a $2\times 2$ real array with $\det e\neq 0$ and let $a_1,a_2$ be non-zero reals. Then, with $\rho=(e^{-1}_{10},e^{-1}_{11})$ the second row of $e^{-1}$, the Lebesgue integral over $v\in\mathbb{R}^2$ of $$S\Bigl(e\cdot\begin{pmatrix}v_0/a_1&0&1\\ v_1/a_1&a_2^{-1}&0\end{pmatrix}\Bigr)\,\psi_\infty\bigl(-v_1\bigr),$$ where $-v_1$ enters through the diagonal embedding [`AutomorphicForm.StandardKernel.ofReal`](def/AutomorphicForm_SmoothingKernel.html#L774) of a real number into the infinite adeles, equals $$(e_{00}+\varepsilon' i e_{10})^n\,e^{-\pi\left(a_2^{-2}(e_{01}^2+e_{11}^2)+e_{00}^2+e_{10}^2\right)}\,\frac{a_1^2}{|\det e|}\,\Bigl(-i\bigl[a a_1(\rho_0-i\rho_1)+a_2^{-1}(e_{01}-ie_{11})\bigr]\Bigr)^m e^{-\pi a^2a_1^2(\rho_0^2+\rho_1^2)}.$$ Only the value of the integral is asserted; no integrability statement is made.
--
--   This is the archimedean inner (Godement) integral of the degree-$m$ flat section built from a conjugate-block harmonic, a column harmonic of degree $n$ and the Gaussian, evaluated in the $(3,1)$-dual configuration of the $2\times 3$ argument; it is a Hecke–Bochner type closed form, obtained from the two-dimensional Fourier transform of a harmonic polynomial times a Gaussian. It is used in the Rankin–Selberg step [`LanglandsTunnell.RankinSelberg.dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3), where the dual torus pair is rewritten as a constant times an integral over the scaled shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_conjBlockHarmonic_pow_colHarmonic_gaussian3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction MeasureTheory

theorem LanglandsTunnell.CubicInduction.integral_dualConfig_eq_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (n m : ℕ) (ε' : ℝ) (hε' : ε' = 1 ∨ ε' = -1) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : a₂ ≠ 0) :
    (∫ v : Fin 2 → ℝ,
        S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
          psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1))))
      = (((e 0 0 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ n *
          (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
          (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
          (-Complex.I *
            ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) - Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
              (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) - Complex.I * ((e 1 1 : ℝ) : ℂ)))) ^ m *
          (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ) := by sorry
