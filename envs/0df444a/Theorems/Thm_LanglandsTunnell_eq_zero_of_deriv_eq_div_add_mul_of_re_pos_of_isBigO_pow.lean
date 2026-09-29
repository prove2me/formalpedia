-- Prove2me | Theorems.Thm_LanglandsTunnell_eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow
-- name    : LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/2ec68e08-8afd-5fef-83ec-1fb4636a6368
-- title:
--   Polynomially bounded solutions of f'=(α/t+β)f vanish when Reβ>0
-- statement:
--   Let $\alpha,\beta\in\mathbb{C}$ with $\operatorname{Re}\beta>0$, and let $f\colon\mathbb{R}\to\mathbb{C}$ be a function which is differentiable on the open half-line $(0,\infty)$ in the sense of `DifferentiableOn ℝ f (Set.Ioi 0)`. Assume that $f$ satisfies the first-order linear equation $\mathrm{deriv}\,f(t)=\bigl(\alpha/t+\beta\bigr)f(t)$ for every real $t>0$, where $t$ is coerced into $\mathbb{C}$ and `deriv` is the (unrestricted) derivative of $f$ at $t$. Assume further that there are a real constant $C$ and a natural number $N$ with $\lVert f(t)\rVert\le C\,t^{N}$ for every real $t\ge 1$. The conclusion is that $f(t)=0$ for every $t>0$. Note that the growth hypothesis is stated as this explicit polynomial bound on $[1,\infty)$, rather than as a `IsBigO` assertion along `atTop`, and that no assertion is made about the values of $f$ at $t\le 0$.
--
--   An elementary uniqueness-and-growth statement for the first-order equation $y'=(\alpha/t+\beta)y$, whose solutions are the multiples of $t^{\alpha}e^{\beta t}$: in the presence of $\operatorname{Re}\beta>0$ a moderate-growth solution must be trivial. It is used in the analysis of Whittaker coefficients, being cited by [`AutomorphicForm.whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero`](thm.html#AutomorphicForm.whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero) to rule out the exponentially growing solution of the lowest-weight equation on one half-line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow
    (α β : ℂ) (hβ : 0 < β.re) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hfeq : ∀ t : ℝ, 0 < t → deriv f t = (α / (t : ℂ) + β) * f t)
    (C : ℝ) (N : ℕ) (hgrowth : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * t ^ N) :
    ∀ t : ℝ, 0 < t → f t = 0 := by sorry
