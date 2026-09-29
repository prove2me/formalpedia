-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero
-- name    : LanglandsTunnell.Converse.ArchDatumR.exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/cc362eb0-2182-56cf-98b3-dcc49b34c3bd
-- title:
--   Mellin non-vanishing far right for two-sheet torus-kernel transforms
-- statement:
--   Fix a real archimedean parameter $P_2$ (either principal, given by $(u_1,a_1,u_2,a_2)$, or discrete, given by $(u,k)$ with $k\ge 1$) and an archimedean Whittaker datum $D$ for $P_2$: a function $W = D.W$ on real $2\times2$ matrices that is smooth on the invertible locus, satisfies $W(\mathrm{unip}(x)g)=\psi(x)W(g)$ and $W(zg)=\chi_{P_2}(z)\,|z|\,W(g)$ for $z\neq0$, and is equipped with entire zeta functions of finite order satisfying the stated integral representations and functional equation together with decay bounds at $0$ and $\infty$; here $\chi_{P_2} =$ `ArchR.centralChar P₂` is the quasi-character attached to the central exponent and central sign of $P_2$. Let $a\in\mathbb{R}$ with $a\neq 0$, let $\nu\in\mathbb{C}$, and let $\varepsilon\in\mathbb{C}$ with $\varepsilon=1$ or $\varepsilon=-1$. Assume the two-sheet combination of the torus profile does not vanish identically on the positive axis: there is $\tau>0$ with $W(\mathrm{diag}(\tau,1))+\varepsilon\,W(\mathrm{diag}(-\tau,1))\neq0$. Let $H:\mathbb{R}\to\mathbb{C}$ be given by $$H(\sigma')=e^{-\pi a^2\sigma'^2}\int_0^\infty\bigl(W(\mathrm{diag}(a\sigma'/w,1))+\varepsilon W(\mathrm{diag}(-a\sigma'/w,1))\bigr)\,\chi_{P_2}(w)\,|w|\,w^{\nu}\,e^{-\pi(w^{-2}+a^2w^2)}\,dw,$$ and assume $H$ is continuous on $(0,\infty)$. Then for every $x_0\in\mathbb{R}$ there exists $s\in\mathbb{C}$ with $\operatorname{Re} s>x_0$ and $\mathcal{M}H(s-1)=\int_0^\infty t^{s-2}H(t)\,dt\neq0$.
--
--   This is the archimedean non-vanishing input used in the converse-theorem part of the Langlands–Tunnell argument: the Mellin transform of the Gaussian-damped torus-kernel transform of a two-sheet combination $f_D(\tau)+\varepsilon f_D(-\tau)$ of the Whittaker profile cannot vanish on every vertical line arbitrarily far to the right. It is invoked in the cubic-induction step to produce admissible twists for which the relevant archimedean zeta and Jacquet vector are non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open LanglandsTunnell.Converse.ArchR Set in

theorem LanglandsTunnell.Converse.ArchDatumR.exists_lt_re_mellin_gaussian_mul_integral_twoSheet_torusKernel_ne_zero
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) (ν : ℂ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (hg : ∃ τ : ℝ, 0 < τ ∧ D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ)) ≠ 0)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne (a * (σ' / w))) + ε * D.W (ArchR.diagOne (-(a * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ν *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (hHc : ContinuousOn H (Set.Ioi 0)) (x₀ : ℝ) :
    ∃ s : ℂ, x₀ < s.re ∧ mellin H (s - 1) ≠ 0 := by sorry
