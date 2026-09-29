-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_dualConfig_detPow_colHarmonic_eq_two_pi_mul_integral_iwasawa_of_archWeightChar
-- name    : LanglandsTunnell.Converse.integral_dualConfig_detPow_colHarmonic_eq_two_pi_mul_integral_iwasawa_of_archWeightChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/3289a4d0-dacd-5874-93ab-eeeb3d2d84ed
-- title:
--   Iwasawa form of the dual-configuration integral at weight k₀=n
-- statement:
--   Fix a real archimedean parameter $P_2$ (principal or discrete) and an archimedean Whittaker datum $D$ for it, i.e. a function $W = D.W$ on $2\times2$ real matrices which is smooth on the invertible locus, satisfies $W(u(x)g)=\psi(x)W(g)$ with $\psi(x)=e^{2\pi i x}$, satisfies $W(zg)=\chi_{P_2}(z)|z|\,W(g)$ for $z\ne0$ with $\chi_{P_2}$ the central quasi-character of $P_2$, and has the entire zeta functions, functional equation, growth and decay properties required by `ArchDatumR`. Let $k_0\in\mathbb Z$, $n\in\mathbb N$ with $k_0=n$, and $\delta\in\{0,1\}$. Assume $W$ has weight $k_0$ on the right: $W(xr)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(r)\,W(x)$ for all $r$ in `rowIsometrySubgroup₀ ℝ` and all $x\in GL_2(\mathbb R)$ (the ambient row-isometry group consisting of $k$ with $|\det k|=1$ acting isometrically on row vectors). Let $a\ne0$, $u\in\mathbb C$, $a_0\in\mathbb Z/2$ (giving the quasi-character $\chi_{u,a_0}(y)=|y|^u$ times $\operatorname{sign}(y)$ when $a_0\ne0$), $a_1\ne0$ and $a_2>0$, and assume the Iwasawa-coordinate integrand displayed on the right-hand side is integrable on $\mathbb R\times\mathbb R\times(0,\infty)$ for Lebesgue measure. Then the Lebesgue integral over $e\in M_2(\mathbb R)\cong\mathbb R^4$ of $$(e_{00}-ie_{10})^n e^{-\pi(a_2^{-2}(e_{01}^2+e_{11}^2)+e_{00}^2+e_{10}^2)}\,a_1^2|\det e|^{-1}\bigl(-i\,aa_1a_2^{-1}(e_{11}(e^{-1})_{10}-e_{01}(e^{-1})_{11})\bigr)^{\delta} e^{-\pi a^2a_1^2((e^{-1})_{10}^2+(e^{-1})_{11}^2)}\cdot\chi_{u,a_0}(\det e)|\det e|^{-2}\cdot W\bigl(\mathrm{diag}(a,1)\,e^{-1}\bigr)$$ equals $2\pi$ times the iterated integral over $y_1\in\mathbb R$, $y_2\in(0,\infty)$, $x\in\mathbb R$ of $$e^{-\pi(a_2^{-2}(x^2/y_1^2+1/y_2^2)+1/y_1^2)}a_1^2|y_1y_2|\,y_1^{-n}\bigl(-i\,aa_1a_2^{-1}xy_2/y_1\bigr)^{\delta}e^{-\pi a^2a_1^2y_2^2}\cdot\chi_{u,a_0}((y_1y_2)^{-1})|y_1y_2|^{2}\cdot\psi(ax)\,\chi_{P_2}(y_2)|y_2|\,W(\mathrm{diag}(ay_1/y_2,1))\cdot y_2^2|y_1y_2|^{-4},$$ where $\mathrm{diag}(y,1)$ denotes the matrix $\begin{pmatrix}y&0\\0&1\end{pmatrix}$.
--
--   This is the archimedean unfolding step for the even (determinant-power, harmonic-column) Schwartz section: the four-dimensional integral over $2\times2$ real matrices in dual-configuration coordinates is rewritten in Iwasawa coordinates $(x,y_1,y_2,\theta)$, the integrand being independent of $\theta$ because the column factor $(e_{00}-ie_{10})^n$ cancels the weight-$k_0$ character with $k_0=n$, so that the circle variable contributes the constant $2\pi$. It feeds the three computations of the archimedean dual torus pair against the gamma factor used in the converse-theorem input to Langlands–Tunnell, and it cites the Iwasawa change of variables on $M_2(\mathbb R)$, the $\theta$-free set-integral identity and the transformation law of $W$ along $\mathrm{diag}(c,1)$ times an Iwasawa matrix.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_dualConfig_detPow_colHarmonic_eq_two_pi_mul_integral_iwasawa_of_archWeightChar.lean

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

theorem LanglandsTunnell.Converse.integral_dualConfig_detPow_colHarmonic_eq_two_pi_mul_integral_iwasawa_of_archWeightChar
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (k₀ : ℤ) (n : ℕ) (hk : k₀ = (n : ℤ)) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂)
    (hInt : Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    (∫ e : Fin 2 → Fin 2 → ℝ,
        ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ n *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    ((-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((e 1 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) - ((e 0 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)))) ^ δ) *
                    (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar u a₀ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne a * (Matrix.of e)⁻¹)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((x * y₂ / y₁ : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by sorry
