-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_detPow_colHarmonic
-- name    : LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_detPow_colHarmonic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/45bfb640-be96-5bb2-999b-1b63c3b93c92
-- title:
--   Integrability of the dual Iwasawa integrand for the det^δ section
-- statement:
--   Let $P_2$ be a real archimedean parameter (principal or discrete), let $D$ be a real archimedean Whittaker datum for $P_2$, i.e. a function $W$ on $2\times2$ real matrices that is smooth on the invertible locus, satisfies $W(\mathrm{unip}(x)g)=e^{2\pi i x}W(g)$ and the central law $W(zg)=\chi_{P_2}(z)|z|\,W(g)$ for $z\ne0$, and carries the zeta-integral, functional-equation, finite-order and torus-decay data of `ArchDatumR`. Let $a\ne0$ and $a_1\ne0$ be real, $a_2>0$, $u\in\mathbb{C}$, $a_0\in\mathbb{Z}/2$, $n\in\mathbb{N}$, and $\delta\in\{0,1\}$. Then the function of $q=(x,y_1,y_2)\in\mathbb{R}\times\mathbb{R}\times\mathbb{R}$ given by the product of $\exp\bigl(-\pi(a_2^{-2}(x^2/y_1^2+1/y_2^2)+1/y_1^2)\bigr)$, $a_1^2|y_1y_2|$, $y_1^{-n}\bigl(-i\,a\,a_1a_2^{-1}\,xy_2/y_1\bigr)^{\delta}$, $\exp(-\pi a^2a_1^2y_2^2)$, the quasicharacter value $|y_1y_2|^{-u}$ times $1$ or $\mathrm{sign}((y_1y_2)^{-1})$ according as $a_0=0$ or not, the factor $|y_1y_2|^{2}$, $e^{2\pi i a x}$, $\chi_{P_2}(y_2)|y_2|$ (the central quasicharacter of $P_2$ at $y_2$), $W(\mathrm{diag}(ay_1/y_2,1))$ and $y_2^2|y_1y_2|^{-4}$, is integrable for Lebesgue measure in $x$ and $y_1$ and Lebesgue measure restricted to $(0,\infty)$ in $y_2$.
--
--   This is the integrability hypothesis needed to rewrite the archimedean dual-configuration integral of the even (determinant-power, column-harmonic) section in Iwasawa coordinates. It is used in the three computations of the archimedean dual torus pair as the archimedean root number times an explicit factor times a gamma factor, for the discrete, weight-one and weight-zero profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_detPow_colHarmonic.lean

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

theorem LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_detPow_colHarmonic
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂) (n : ℕ) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * (-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ))) ^ δ) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
