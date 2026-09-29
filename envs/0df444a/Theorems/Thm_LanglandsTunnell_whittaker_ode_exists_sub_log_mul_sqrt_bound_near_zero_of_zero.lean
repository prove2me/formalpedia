-- Prove2me | Theorems.Thm_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero
-- name    : LanglandsTunnell.whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/fa65ea0d-3d96-5390-a2aa-fd2de82ebc78
-- title:
--   Logarithmic two-term behaviour at 0 for the Whittaker equation
-- statement:
--   Fix a real number $\kappa$ and a function $f\colon\mathbb{R}\to\mathbb{C}$. Assume $f$ is differentiable on the open half-line $(0,\infty)$ and that its derivative $\mathrm{deriv}\,f$ is again differentiable on $(0,\infty)$, and assume that for every real $y>0$ the second-order equation $$y^{2}f''(y)+\Bigl(\tfrac14-0^{2}+2\pi\kappa y-4\pi^{2}y^{2}\Bigr)f(y)=0$$ holds, where $y$ and $\kappa$ are coerced into $\mathbb{C}$ and the vanishing parameter is written explicitly as $0^{2}$ (so this is the Whittaker equation with parameters $\kappa$ and $\nu=0$). The conclusion asserts the existence of constants $a,b\in\mathbb{C}$ and a real $\delta>0$ together with a real constant $C$ such that $$\bigl\|f(y)-\bigl(a+b\log y\bigr)\sqrt{y}\bigr\|\le C\,y^{1/2+\delta}\qquad\text{for all }0<y\le 1,$$ and moreover such that, in the case $b=0$, both $y^{-1/2}f(y)\to a$ and $\sqrt{y}\,\bigl(f'(y)-f(y)/(2y)\bigr)\to 0$ as $y\to 0^{+}$ (limits along the filter of right neighbourhoods of $0$, with $(\sqrt{y})^{-1}$ and $\sqrt{y}$ understood as complex scalars).
--
--   This is the Frobenius analysis at the regular singular point $y=0$ of the Whittaker equation with $\nu=0$, the case of a double indicial exponent $\tfrac12$ whose Euler solutions are $\sqrt{y}$ and $\sqrt{y}\log y$: the statement isolates the logarithmic coefficient $b$, with an error term of strictly better order, and records the log-free boundary behaviour of $f$ and of its first derivative when $b$ vanishes. It is used in the argument that a wrong-sign Whittaker solution of moderate growth whose Mellin transform has the prescribed shape must vanish identically, in the limit-of-discrete-series situation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Real Complex Filter Topology

theorem LanglandsTunnell.whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero
    (κ : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - (0 : ℂ) ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ (a b : ℂ) (δ : ℝ), 0 < δ ∧
      (∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ)‖ ≤ C * y ^ (1 / 2 + δ)) ∧
      (b = 0 →
        Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ)⁻¹ * f y) (𝓝[>] 0) (𝓝 a) ∧
        Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ) * (deriv f y - f y / (2 * (y : ℂ)))) (𝓝[>] 0) (𝓝 0)) := by sorry
