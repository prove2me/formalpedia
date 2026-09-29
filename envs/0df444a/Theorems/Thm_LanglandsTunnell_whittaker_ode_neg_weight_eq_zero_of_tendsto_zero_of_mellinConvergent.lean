-- Prove2me | Theorems.Thm_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_tendsto_zero_of_mellinConvergent
-- name    : LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_tendsto_zero_of_mellinConvergent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/e8bb04c3-158e-508b-bf6a-2524840e1591
-- title:
--   Vanishing of decaying L¹-Mellin solutions of the negative-weight Whittaker equation
-- statement:
--   Let $\nu$ be a complex number such that $\nu^2$ has vanishing imaginary part and real part at least $1/4$ (so $\nu^2$ is real and $\nu^2 \ge 1/4$), let $k$ be a real number with $k > 0$, and let $f : \mathbb{R} \to \mathbb{C}$ be a function which is differentiable on $(0,\infty)$ and whose derivative is again differentiable on $(0,\infty)$. Assume that for every $y > 0$ one has $$y^2 f''(y) + \bigl(\tfrac14 - \nu^2 + 2\pi(-k)y - 4\pi^2 y^2\bigr) f(y) = 0,$$ that is, the Whittaker-type equation with the linear term carrying the sign $-2\pi k y$, where $y$ and $-k$ are coerced into $\mathbb{C}$. Assume further that $f(y) \to 0$ as $y \to 0^+$ (limit along the filter of right-hand neighbourhoods of $0$), and that for some real $s_1 \ge 0$ the function $f$ is Mellin convergent at the point $s_1 \in \mathbb{C}$, i.e. $t \mapsto t^{s_1 - 1} f(t)$ is integrable on $(0,\infty)$. Then $f(y) = 0$ for every $y > 0$.
--
--   This is the uniqueness (vanishing) statement for the Whittaker equation with the wrong sign of the linear term: in the range $\nu^2 \ge 1/4$, $k>0$ no nonzero solution can both decay at the origin and have an absolutely convergent Mellin integral, the recessive Whittaker function $M_{\kappa,\nu}$ with $\kappa<0$ growing too fast at infinity. It is used in the step [`LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul`](thm.html#LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul), which rules out wrong-sign Whittaker coefficients in the analytic input to the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_tendsto_zero_of_mellinConvergent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Real Complex Filter Topology MeasureTheory

theorem LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_tendsto_zero_of_mellinConvergent
    (ν : ℂ) (hν : (ν ^ 2).im = 0) (hν' : 1 / 4 ≤ (ν ^ 2).re) (k : ℝ) (hk : 0 < k) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((-k : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (h0 : Tendsto f (𝓝[>] 0) (𝓝 0))
    (s₁ : ℝ) (hs₁ : 0 ≤ s₁) (hmel : MellinConvergent f (s₁ : ℂ))
    (y : ℝ) (hy : 0 < y) : f y = 0 := by sorry
