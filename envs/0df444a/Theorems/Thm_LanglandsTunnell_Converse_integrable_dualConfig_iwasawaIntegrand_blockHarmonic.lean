-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_blockHarmonic
-- name    : LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_blockHarmonic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/b32d1e30-cd0c-5fe1-898e-26a999e91eb8
-- title:
--   Integrability of the block-harmonic dual Iwasawa integrand
-- statement:
--   Let $P_2$ be a real archimedean parameter (either a principal parameter given by exponents $u_1,u_2\in\mathbb{C}$ and signs in $\mathbb{Z}/2$, or a discrete parameter given by $u\in\mathbb{C}$ and a weight $k\ge 1$), and let $D$ be an archimedean Whittaker datum for $P_2$: a function $W$ on real $2\times 2$ matrices, smooth on the invertible locus, satisfying $W(n(x)g)=e^{2\pi i x}W(g)$ and $W(zg)=\chi_{P_2}(z)\,|z|\,W(g)$ for $z\ne 0$, whose zeta integrals converge in a right half-plane, equal the archimedean $\Gamma$-factor of the twisted parameter times an entire function of finite order satisfying the expected functional equation, and whose derivatives along the torus decay rapidly as $|y|\to\infty$ and at most polynomially as $y\to 0$. Let $a\ne 0$ be real, $u\in\mathbb{C}$, $a_0\in\mathbb{Z}/2$, and let $a_1\ne 0$ and $a_2>0$ be real. Then the function of $q=(x,y_1,y_2)$ given by $$e^{-\pi\left(a_2^{-2}(x^2/y_1^2+1/y_2^2)+1/y_1^2\right)}\,a_1^2|y_1y_2|\cdot \frac{1}{y_1}\Bigl(a a_1 y_2+\frac{a_2^{-1}}{y_2}+i\,a_2^{-1}\frac{x}{y_1}\Bigr)\,e^{-\pi a^2a_1^2y_2^2}$$ multiplied by $|(y_1y_2)^{-1}|^{u}\,\varepsilon_{a_0}((y_1y_2)^{-1})\cdot\bigl(|(y_1y_2)^{-1}|^2\bigr)^{-1}$ (where $\varepsilon_{a_0}$ is $1$ if $a_0=0$ and the sign character otherwise), by $e^{2\pi i a x}$, by $\chi_{P_2}(y_2)\,|y_2|$, by $W\!\left(\mathrm{diag}(a y_1/y_2,\,1)\right)$, and by $y_2^2\,|y_1y_2|^{-4}$, is integrable for the product of Lebesgue measure in $x$, Lebesgue measure in $y_1$ and Lebesgue measure restricted to $(0,\infty)$ in $y_2$.
--
--   This is the absolute convergence statement for the dual Iwasawa-coordinate integrand occurring in the block-harmonic (major) section of the archimedean Rankin–Selberg torus pair, the $\theta$-free form obtained after the angular integration. It is used in the evaluation of the dual torus pair in terms of the archimedean root number, an explicit factor and a $\Gamma$-factor for weight-one data with block-harmonic and column-harmonic Gaussian profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_blockHarmonic.lean

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

theorem LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_blockHarmonic
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (q.2.2 : ℂ) + (a₂⁻¹ : ℂ) * ((q.2.2⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((q.1 / q.2.1 : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
