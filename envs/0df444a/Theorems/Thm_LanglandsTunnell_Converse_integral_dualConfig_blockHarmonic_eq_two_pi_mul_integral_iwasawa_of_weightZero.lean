-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero
-- name    : LanglandsTunnell.Converse.integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/b299fcc9-96fa-5147-a36b-b1819ab1d628
-- title:
--   Dual configuration integral equals 2π times Iwasawa integral
-- statement:
--   Fix a real archimedean parameter $P_2$ and a datum $D$ of type `ArchDatumR P₂`, i.e. a Whittaker function $W\colon M_2(\mathbb R)\to\mathbb C$, smooth on the invertible locus, satisfying $W(n(x)g)=e^{2\pi i x}W(g)$, $W(zg)=\chi_{P_2}(z)\,|z|\,W(g)$ for $z\neq0$ (where $\chi_{P_2}(y)=|y|^{u}\cdot(\mathrm{sign}\,y)^{\varepsilon}$ is built from the central exponent and sign of $P_2$), together with the package of zeta integrals, their entirety, functional equation, finite order and decay estimates at $0$ and $\infty$. Assume $W$ is right invariant under the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb R)$. Let $a\neq 0$, $u\in\mathbb C$, $a_0\in\mathbb Z/2$, $a_1\neq0$, $a_2>0$ be given, and assume the stated integrability of the $\theta$-free integrand on $\mathbb R\times\mathbb R\times(0,\infty)$ for the product of Lebesgue measures. Then the Lebesgue integral over $e\in M_2(\mathbb R)$ of
--   $$(e_{00}-ie_{10})\,e^{-\pi(a_2^{-2}(e_{01}^2+e_{11}^2)+e_{00}^2+e_{10}^2)}\,\frac{a_1^2}{|\det e|}\Bigl(-i\bigl(aa_1(\rho_0+i\rho_1)+a_2^{-1}(e_{01}+ie_{11})\bigr)\Bigr)e^{-\pi a^2a_1^2(\rho_0^2+\rho_1^2)}\cdot\chi_{u,a_0}(\det e)\,|\det e|^{-2}\,W\bigl(\mathrm{diag}(a,1)e^{-1}\bigr),$$
--   with $\rho=(\rho_0,\rho_1)$ the second row of $e^{-1}$ and $\chi_{u,a_0}(t)=|t|^{u}$ times $1$ or $\mathrm{sign}\,t$ according as $a_0=0$ or not, equals $2\pi$ times the iterated integral $\int_{y_1\in\mathbb R}\int_{y_2>0}\int_{x\in\mathbb R}$ of
--   $$e^{-\pi(a_2^{-2}(x^2/y_1^2+1/y_2^2)+1/y_1^2)}\,a_1^2|y_1y_2|\,y_1^{-1}\bigl(aa_1y_2+a_2^{-1}y_2^{-1}+i a_2^{-1}x/y_1\bigr)e^{-\pi a^2a_1^2y_2^2}\cdot\chi_{u,a_0}\bigl((y_1y_2)^{-1}\bigr)|(y_1y_2)^{-1}|^{-2}\cdot e^{2\pi i a x}\,\chi_{P_2}(y_2)|y_2|\,W\bigl(\mathrm{diag}(ay_1/y_2,1)\bigr)\cdot\frac{y_2^2}{|y_1y_2|^{4}}.$$
--
--   This is the passage to Iwasawa coordinates $e=(n(x)\,\mathrm{diag}(y_1,y_2)\,\kappa_\theta)^{-1}$ for the archimedean matrix integral attached to the dual Godement configuration of the block-harmonic section: the angular variable drops out of the integrand, the $\theta$-integration contributing the factor $2\pi$. It feeds the evaluation of the dual torus pair in the weight-one Rankin–Selberg computation of the archimedean root number and gamma factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂)
    (hInt : Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (q.2.2 : ℂ) + (a₂⁻¹ : ℂ) * ((q.2.2⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((q.1 / q.2.1 : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    (∫ e : Fin 2 → Fin 2 → ℝ,
        ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ 1 *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    (-Complex.I *
                      ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
                        (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ)))) *
                    (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar u a₀ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne a * (Matrix.of e)⁻¹)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by sorry
