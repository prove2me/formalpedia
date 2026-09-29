-- Prove2me | Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing
-- name    : LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/a7094bb0-9ef1-50a6-9fe0-7c70fe7996fb
-- title:
--   Near-zero decay for a forced first-order Euler equation
-- statement:
--   Let $b \in \mathbb{C}$, let $\sigma, A \in \mathbb{R}$, and let $f, h \colon \mathbb{R} \to \mathbb{C}$ be functions such that: $f$ is differentiable on the open half-line $(0,\infty)$; the forcing term satisfies $\|h(y)\| \le A\,y^{\sigma}$ for all $y$ with $0 < y \le 1$ (the power being the real `rpow`); and the Euler relation $y\,f'(y) = b\,f(y) + h(y)$ holds for every $y > 0$, where $f'$ is the Mathlib derivative `deriv f` and $y$ is coerced into $\mathbb{C}$. The conclusion is that for every $\varepsilon > 0$ there exists a real constant $C$ such that $\|f(y)\| \le C\,y^{\min(\operatorname{Re} b,\, \sigma) - \varepsilon}$ for all $y$ with $0 < y \le 1$. No sign or size condition is imposed on $A$, $\sigma$ or $b$, the constant $C$ is merely asserted to exist (no normalisation or positivity is claimed), and the bound on $f$ is asserted only on $(0,1]$, the range where the hypothesis on $h$ is available.
--
--   This is the standard near-zero estimate for a solution of the forced first-order Euler (regular singular) equation $y f' = b f + h$: the solution decays with the exponent $\min(\operatorname{Re} b, \sigma)$, the $\varepsilon$ absorbing the logarithm that appears in the resonant case $\sigma = \operatorname{Re} b$. It is used in the analytic input to the Langlands–Tunnell step, where it is invoked by [`LanglandsTunnell.exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded`](thm.html#LanglandsTunnell.exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded) to propagate decay along a first-order relation between neighbouring weights.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing
    (b : ℂ) (σ A : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = b * f y + h y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (min b.re σ - ε) := by sorry
