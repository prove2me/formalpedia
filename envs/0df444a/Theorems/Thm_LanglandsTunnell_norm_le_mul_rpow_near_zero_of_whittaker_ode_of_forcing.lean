-- Prove2me | Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing
-- name    : LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/e3223bd0-a959-56fb-b3b8-066d11a41340
-- title:
--   Near-zero bound for forced Whittaker equation solutions
-- statement:
--   Let $\nu \in \mathbb{C}$, let $k, \sigma, A \in \mathbb{R}$, and let $f, h : \mathbb{R} \to \mathbb{C}$. Assume $f$ is differentiable on the open ray $(0,\infty)$ and that its derivative $\operatorname{deriv} f$ is again differentiable there; assume the forcing term satisfies $\|h(y)\| \le A\,y^{\sigma}$ for all $y$ with $0 < y \le 1$; and assume that for every $y > 0$ the second-order equation
--   $$y^{2} f''(y) + \Bigl(\tfrac14 - \nu^{2} + 2\pi k y - 4\pi^{2} y^{2}\Bigr) f(y) = h(y)$$
--   holds, where $y$ and $k$ are read as complex numbers and $f''$ denotes the iterated derivative $\operatorname{deriv}(\operatorname{deriv} f)$. The conclusion is that for every $\varepsilon > 0$ there exists a real constant $C$ such that $\|f(y)\| \le C\, y^{\min(1/2 - |\operatorname{Re}\nu|,\ \sigma) - \varepsilon}$ for all $y$ with $0 < y \le 1$. No continuity of $h$ beyond the stated bound on $(0,1]$ is assumed, no behaviour of $f$ as $y \to \infty$ is assumed, and the constant $C$ is merely asserted to exist, with no sign or explicit dependence claimed.
--
--   This is the local analysis at the regular singular point $y = 0$ of the inhomogeneous Whittaker equation (for $k = 0$, the modified Bessel equation), whose indicial exponents are $\tfrac12 \pm \nu$: a forcing of size $O(y^{\sigma})$ produces a response of size $O(y^{\sigma})$ together with free modes of size $O(y^{1/2 - |\operatorname{Re}\nu|})$, the logarithmic losses at the resonant parameter values being absorbed into the arbitrarily small $\varepsilon$. It feeds the uniform bounds on Whittaker coefficients of torus vectors used in [`LanglandsTunnell.exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos`](thm.html#LanglandsTunnell.exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing
    (ν : ℂ) (k σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min (1 / 2 - |ν.re|) σ - ε) := by sorry
