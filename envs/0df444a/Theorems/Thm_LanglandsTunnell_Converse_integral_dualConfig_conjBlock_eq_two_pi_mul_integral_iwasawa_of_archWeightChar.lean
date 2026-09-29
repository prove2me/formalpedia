-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_dualConfig_conjBlock_eq_two_pi_mul_integral_iwasawa_of_archWeightChar
-- name    : LanglandsTunnell.Converse.integral_dualConfig_conjBlock_eq_two_pi_mul_integral_iwasawa_of_archWeightChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/cb2a7167-97eb-5c99-b1c5-b529ba6d86e1
-- title:
--   Dual Godement integral in Iwasawa coordinates, weight n+1
-- statement:
--   Fix a real archimedean parameter $P_2$ (a `RealArchParam`, either a principal pair $(u_1,a_1,u_2,a_2)$ or a discrete datum $(u,k)$ with $1\le k$) and a real archimedean Whittaker datum $D$ for $P_2$, i.e. a function $W=D.W$ on $M_2(\mathbb R)$, smooth on the invertible locus, with $W(n(x)g)=\psi(x)W(g)$ where $\psi(x)=e^{2\pi i x}$, with $W(zg)=\chi_{P_2}(z)|z|W(g)$ for $z\ne0$ (here $\chi_{P_2}(y)=|y|^{u}\cdot(1$ or $\operatorname{sign} y)$ for the central exponent and sign of $P_2$), and with the attached zeta integrals converging, entire of finite order, satisfying the functional equation with the $\varepsilon$-factor of $P_2$ and the stated derivative bounds at $0$ and $\infty$. Let $k_0\in\mathbb Z$, $n\in\mathbb N$ with $k_0=n+1$, and assume the rotation law $W(xr)=\operatorname{archWeightChar}_{\mathbb R}(k_0)(r)\,W(x)$ for all $x\in GL_2(\mathbb R)$ and all $r$ in the subgroup `rowIsometrySubgroup₀ ℝ`. Let $a\ne0$, $u\in\mathbb C$, $a_0\in\mathbb Z/2$, $a_1\ne0$, $a_2>0$, and write $\chi_{u,a_0}(y)=|y|^{u}\cdot(1$ if $a_0=0$, else $\operatorname{sign} y)$. Define, for $x,y_1,y_2$ real, the $\theta$-free Iwasawa integrand
--   $$G(x,y_1,y_2)=e^{-\pi\left(a_2^{-2}(x^2/y_1^2+1/y_2^2)+1/y_1^2\right)}\,a_1^2|y_1y_2|\,y_1^{-n}\!\left(-aa_1y_2-\frac{1}{a_2y_2}+\frac{ix}{a_2y_1}\right)e^{-\pi a^2a_1^2y_2^2}\,\chi_{u,a_0}\!\left((y_1y_2)^{-1}\right)|(y_1y_2)^{-1}|^{-2}\,\psi(ax)\,\chi_{P_2}(y_2)|y_2|\,W\!\left(\operatorname{diag}(ay_1/y_2,1)\right)\frac{y_2^{2}}{|y_1y_2|^{4}},$$
--   and assume $G$ is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$ for the product of Lebesgue measures. Then the Lebesgue integral over all $e\in M_2(\mathbb R)$ of
--   $$(e_{00}-ie_{10})^{n}e^{-\pi\left(a_2^{-2}(e_{01}^2+e_{11}^2)+e_{00}^2+e_{10}^2\right)}\frac{a_1^2}{|\det e|}\left(-i\left(aa_1(\rho_0-i\rho_1)+a_2^{-1}(e_{01}-ie_{11})\right)\right)e^{-\pi a^2a_1^2(\rho_0^2+\rho_1^2)}\chi_{u,a_0}(\det e)|\det e|^{-2}\,W\!\left(\operatorname{diag}(a,1)e^{-1}\right),$$
--   where $(\rho_0,\rho_1)$ is the second row of $e^{-1}$, equals $2\pi\int_{y_1\in\mathbb R}\int_{y_2>0}\int_{x\in\mathbb R}G(x,y_1,y_2)$, the integrals taken in that order.
--
--   This is the passage to Iwasawa coordinates $e=(n(x)\operatorname{diag}(y_1,y_2)\kappa_\theta)^{-1}$ for the archimedean dual Godement integral attached to the conjugate-block flat section of weight $k_0=n+1$: the weight-$k_0$ rotation law makes the integrand independent of $\theta$, so the angular variable contributes the factor $2\pi$. It feeds the computations of the dual torus pair at weight one in the Rankin–Selberg analysis used for the converse theorem in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_dualConfig_conjBlock_eq_two_pi_mul_integral_iwasawa_of_archWeightChar.lean

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

theorem LanglandsTunnell.Converse.integral_dualConfig_conjBlock_eq_two_pi_mul_integral_iwasawa_of_archWeightChar
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (k₀ : ℤ) (n : ℕ) (hk : k₀ = (n : ℤ) + 1)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂)
    (hInt : Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * (-((a : ℂ) * (a₁ : ℂ) * (q.2.2 : ℂ)) - (a₂⁻¹ : ℂ) * ((q.2.2⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((q.1 / q.2.1 : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    (∫ e : Fin 2 → Fin 2 → ℝ,
        ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ n *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    (-Complex.I *
                      ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) - Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) +
                        (a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) - Complex.I * ((e 1 1 : ℝ) : ℂ)))) *
                    (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar u a₀ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne a * (Matrix.of e)⁻¹)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) ^ n * (-((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ)) - (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by sorry
