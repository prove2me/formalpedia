-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_conjBlock
-- name    : LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_conjBlock
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/1d1acc52-a7ad-552d-9192-bc12a4f17efc
-- title:
--   Integrability of the conjugate-block dual Iwasawa integrand
-- statement:
--   Let $P_2$ be a real archimedean parameter and let $D$ be an archimedean Whittaker datum for $P_2$, i.e. a function $W = D.W$ on real $2\times 2$ matrices that is smooth on the general linear locus, satisfies $W(u(x)g) = \psi(x)W(g)$ with $\psi(x) = e^{2\pi i x}$ and the central law $W(zg) = \chi_{P_2}(z)\,|z|\,W(g)$ for $z \neq 0$, and whose associated zeta integrals are integrable in a right half-plane, equal $\Gamma$-factor times an entire function satisfying a functional equation and of finite order, with the prescribed derivative decay bounds as $|y| \to \infty$ and $y \to 0$ along $\mathrm{diag}(y,1)K$. Let $a \in \mathbb{R}$ with $a \neq 0$, $u \in \mathbb{C}$, $a_0 \in \mathbb{Z}/2$, $a_1, a_2 \in \mathbb{R}$ with $a_1 \neq 0$ and $a_2 > 0$, and $n \in \mathbb{N}$. The assertion is that the function of $q = (x, y_1, y_2)$ given by $$e^{-\pi\left(a_2^{-2}(x^2/y_1^2 + y_2^{-2}) + y_1^{-2}\right)}\, a_1^2 |y_1 y_2| \, y_1^{-n}\left(-a a_1 y_2 - a_2^{-1} y_2^{-1} + i\,a_2^{-1} x/y_1\right) e^{-\pi a^2 a_1^2 y_2^2} \cdot \chi_{u,a_0}\big((y_1y_2)^{-1}\big)\,|y_1y_2|^{2} \cdot \psi(ax)\,\chi_{P_2}(y_2)\,|y_2|\;W\!\left(\mathrm{diag}(a y_1/y_2,\,1)\right) \cdot y_2^2 |y_1y_2|^{-4}$$ is integrable on $\mathbb{R} \times \mathbb{R} \times (0,\infty)$ for Lebesgue measure (the third factor being Lebesgue measure restricted to $(0,\infty)$). Here $\chi_{u,a_0}(y) = |y|^{u}$ times $1$ if $a_0 = 0$ and $\mathrm{sign}(y)$ otherwise, $\chi_{P_2}$ is the corresponding quasicharacter formed from the central exponent and central sign of $P_2$, and $\mathrm{diag}(\tau,1)$ denotes the matrix $\begin{pmatrix}\tau & 0\\ 0 & 1\end{pmatrix}$.
--
--   This supplies the absolute-convergence hypothesis needed to treat the archimedean dual configuration integral of the conjugate-block section in Iwasawa coordinates, the integrand being $s$-free and the decay coming from the axioms of the archimedean Whittaker datum alone. It is cited by the two computations of archimedean root numbers for dual torus pairs at weight one, in the discrete-series and weight-one profile cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_conjBlock.lean

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

theorem LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_conjBlock
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂) (n : ℕ) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ n * (-((a : ℂ) * (a₁ : ℂ) * (q.2.2 : ℂ)) - (a₂⁻¹ : ℂ) * ((q.2.2⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((q.1 / q.2.1 : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by sorry
