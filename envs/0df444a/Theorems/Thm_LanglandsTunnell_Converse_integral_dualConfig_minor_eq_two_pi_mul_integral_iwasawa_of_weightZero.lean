-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_dualConfig_minor_eq_two_pi_mul_integral_iwasawa_of_weightZero
-- name    : LanglandsTunnell.Converse.integral_dualConfig_minor_eq_two_pi_mul_integral_iwasawa_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/55db3a52-73a2-56c8-8fa5-b8c605103170
-- title:
--   Dual Godement integral in Iwasawa coordinates, weight zero
-- statement:
--   Let $P_2$ be a real archimedean parameter (principal, given by $(u_1,a_1,u_2,a_2)$, or discrete, given by $(u,k)$ with $k\ge 1$) and let $D$ be an `ArchDatumR P₂`, i.e. a function $W:M_2(\mathbb R)\to\mathbb C$, smooth on the invertible locus, with $W(n(x)g)=\psi(x)W(g)$ where $\psi(x)=e^{2\pi i x}$ and $W(zg)=\chi_{P_2}(z)|z|W(g)$ for $z\ne 0$, together with its entire zeta data (integrability, functional equation, finite order, decay at $0$ and $\infty$). Assume the weight-zero condition that $W$ is invariant under right multiplication by elements of the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb R)$. Let $a\ne 0$ and $a_1\ne 0$ be real, $a_2>0$, $u\in\mathbb C$ and $a_0\in\mathbb Z/2$, and assume that the explicit $\theta$-free integrand in the variables $(x,y_1,y_2)$ appearing on the right is integrable for $\mathrm{vol}\times\mathrm{vol}\times(\mathrm{vol}|_{(0,\infty)})$. Then the Lebesgue integral over $e\in M_2(\mathbb R)$ of $$e^{-\pi(a_2^{-2}(e_{01}^2+e_{11}^2)+(e_{00}^2+e_{10}^2))}\,\frac{a_1^2}{|\det e|}\Bigl(-iaa_1(\rho_0e_{10}-\rho_1e_{00})+\tfrac{i}{a_2}\det e\Bigr)e^{-\pi a^2a_1^2(\rho_0^2+\rho_1^2)}\,\chi_{u,a_0}(\det e)\,|\det e|^{-2}\,W(\mathrm{diag}(a,1)\,e^{-1}),$$ with $\rho=(\rho_0,\rho_1)$ the second row of $e^{-1}$ and $\chi_{u,a_0}(y)=|y|^{u}$ times $1$ or $\mathrm{sign}(y)$ according as $a_0=0$ or not, equals $2\pi$ times the iterated integral over $y_1\in\mathbb R$, $y_2\in(0,\infty)$, $x\in\mathbb R$ of $$e^{-\pi(a_2^{-2}(x^2/y_1^2+1/y_2^2)+1/y_1^2)}\,a_1^2|y_1y_2|\Bigl(-iaa_1\bigl(-\tfrac{y_2}{y_1}\bigr)+\tfrac{i}{a_2}(y_1y_2)^{-1}\Bigr)e^{-\pi a^2a_1^2y_2^2}\,\chi_{u,a_0}\bigl((y_1y_2)^{-1}\bigr)|(y_1y_2)^{-1}|^{-2}\,\psi(ax)\,\chi_{P_2}(y_2)|y_2|\,W(\mathrm{diag}(ay_1/y_2,1))\,y_2^{2}|y_1y_2|^{-4}.$$
--
--   This is the passage to Iwasawa coordinates $e=(n(x)\,\mathrm{diag}(y_1,y_2)\kappa_\theta)^{-1}$ for the archimedean dual Godement integral attached to the minor section, the $\theta$-integration contributing the factor $2\pi$ because the weight-zero datum is right invariant under the rotation subgroup and the remaining integrand is $\theta$-free. It feeds the computation of the dual torus pair as an archimedean root number times an explicit gamma factor in the weight-one case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_dualConfig_minor_eq_two_pi_mul_integral_iwasawa_of_weightZero.lean

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

theorem LanglandsTunnell.Converse.integral_dualConfig_minor_eq_two_pi_mul_integral_iwasawa_of_weightZero
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂)
    (hInt : Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (-Complex.I * (a : ℂ) * (a₁ : ℂ) * ((-(q.2.2 / q.2.1) : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    (∫ e : Fin 2 → Fin 2 → ℝ,
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    (-Complex.I * (a : ℂ) * (a₁ : ℂ) *
                        ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) * ((e 1 0 : ℝ) : ℂ) - (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ) * ((e 0 0 : ℝ) : ℂ)) +
                      Complex.I * (a₂⁻¹ : ℂ) * (((Matrix.of e).det : ℝ) : ℂ)) *
                    (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar u a₀ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne a * (Matrix.of e)⁻¹)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (-Complex.I * (a : ℂ) * (a₁ : ℂ) * ((-(y₂ / y₁) : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((y₁ * y₂)⁻¹ : ℝ) : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by sorry
