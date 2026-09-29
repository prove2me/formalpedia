-- Prove2me | Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode
-- name    : LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/7ea604f7-ff51-5a30-a0fd-7836ad465ae1
-- title:
--   Near-zero bounds for solutions of Whittaker's equation
-- statement:
--   Let $\nu\in\mathbb{C}$, let $k\in\mathbb{R}$, and let $f:\mathbb{R}\to\mathbb{C}$ be a function which is differentiable on the open half-line $(0,\infty)$ and whose derivative $f'$ is again differentiable there, and suppose that $f$ satisfies Whittaker's equation in the normalisation $$y^{2}f''(y)+\Bigl(\tfrac14-\nu^{2}+2\pi k\,y-4\pi^{2}y^{2}\Bigr)f(y)=0$$ for every real $y>0$ (the coefficients being read in $\mathbb{C}$, with $y$, $k$ and $\pi$ coerced). The conclusion is the conjunction of two assertions about the behaviour of $f$ on $(0,1]$, the powers being real powers of positive reals. First, if $\nu\neq0$ then there exists a real constant $C$ such that $\|f(y)\|\le C\,y^{1/2-|\operatorname{Re}\nu|}$ for all $y$ with $0<y\le1$. Second, without any restriction on $\nu$, for every real $\varepsilon>0$ there exists a real constant $C$ such that $\|f(y)\|\le C\,y^{1/2-|\operatorname{Re}\nu|-\varepsilon}$ for all $y$ with $0<y\le1$. No growth condition at infinity and no hypothesis on $\operatorname{Re}\nu$ are imposed, and the constants are not asserted to be positive or explicit.
--
--   This is the statement that the origin is a regular singular point of Whittaker's equation with indicial exponents $\tfrac12\pm\nu$, so that every solution — not merely the distinguished one behaving like $\sqrt{y}\,K_\nu(2\pi y)$ — is controlled by the larger exponent near $0$, with an $\varepsilon$ loss absorbing the logarithmic factor that occurs at $\nu=0$. It feeds the estimates on torus Whittaker functions used in the Langlands–Tunnell part of the development, being cited by [`LanglandsTunnell.exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos`](thm.html#LanglandsTunnell.exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos) and by [`LanglandsTunnell.whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer`](thm.html#LanglandsTunnell.whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode
    (ν : ℂ) (k : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    (ν ≠ 0 → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (1 / 2 - |ν.re|)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (1 / 2 - |ν.re| - ε)) := by sorry
