-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile
-- name    : LanglandsTunnell.Converse.exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/3e2edd56-c8a3-5b9b-b04d-2592ed7bc886
-- title:
--   Integrability of a one-sided Gaussian torus integrand
-- statement:
--   Let $W:\mathbb{R}\to\mathbb{C}$ and $Q\in\mathbb{C}$ be such that $W(t)=2\,t^{Q}e^{-2\pi t}$ for every real $t>0$ and $W(t)=0$ for every real $t<0$ (no condition is imposed at $t=0$). Let $P_2$ be a real archimedean parameter, i.e. either a principal datum $(u_1,a_1,u_2,a_2)\in\mathbb{C}\times\mathbb{Z}/2\times\mathbb{C}\times\mathbb{Z}/2$ or a discrete datum $(u,k)$ with $k\ge 1$, and let $D$ be an `ArchDatumR` for $P_2$: a function $D.W$ on real $2\times 2$ matrices, smooth on the locus of invertible matrices, satisfying the unipotent law $D.W(n(x)g)=e^{2\pi i x}D.W(g)$ and the central law, equipped with zeta integrals that converge to the right of an abscissa, equal $\Gamma$-factors times entire functions of finite order satisfying the functional equation with the archimedean $\varepsilon$-factor, and subject to the stated decay bounds near the ends of the torus. Let $a\in\mathbb{R}$, $a\neq 0$, and $m\in\mathbb{N}$. Then there exists $\sigma\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\operatorname{Re}s>\sigma$, every $y_1\neq 0$, every $y_2>0$ and every $c_0,c_1\in\mathbb{C}$, the function $$(x,t)\longmapsto e^{-\pi x^2/y_1^2}\,(c_0+c_1 i x)^m\,e^{2\pi i a t x}\cdot W(t)\,D.W\!\left(\begin{smallmatrix} a t y_1/y_2 & 0\\ 0 & 1\end{smallmatrix}\right)\,|t|^{\,s-1/2}\,t^{-2}$$ is integrable on $\mathbb{R}\times\mathbb{R}$ for the product of Lebesgue measures. The abscissa $\sigma$ is chosen before $s$, $y_1$, $y_2$, $c_0$ and $c_1$, so it may depend only on $Q$, $D$, $a$ and $m$.
--
--   This is the absolute-convergence statement underlying the Iwasawa unfolding of an archimedean Rankin–Selberg torus pair, in the case of the one-sided (discrete-series type) torus profile $W$ and a degree-$m$ polynomial block factor in the $x$-variable. It serves as the Fubini hypothesis for the Gaussian moment computation in the $x$-variable, and is cited in the evaluation of the Iwasawa integral for discrete profiles with harmonic block data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.exists_forall_integrable_xPowGaussian_psi_mul_torusPair_of_oneSided_profile
    (W : ℝ → ℂ) (Q : ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → W t = (2 : ℂ) * (t : ℂ) ^ Q * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → W t = 0)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (m : ℕ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ → ∀ c₀ c₁ : ℂ,
      Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (q.1 : ℂ)) ^ m * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne (a * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by sorry
