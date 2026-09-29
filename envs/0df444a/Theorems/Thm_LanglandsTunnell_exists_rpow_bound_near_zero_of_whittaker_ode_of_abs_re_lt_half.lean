-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half
-- name    : LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/dcb518dc-ac48-5508-8963-bf00bcb5ed38
-- title:
--   Power bound near zero for solutions of the Whittaker equation
-- statement:
--   Let $\nu$ be a complex number whose real part satisfies $|\mathrm{Re}\,\nu| < 1/2$, let $k$ be a real number, and let $f : \mathbb{R} \to \mathbb{C}$ be a function which is differentiable on the open half-line $(0,\infty)$ and whose derivative $f'$ (the Lean `deriv`, taken with respect to the real variable) is again differentiable on $(0,\infty)$. Assume that for every real $y > 0$ one has
--   $$y^{2} f''(y) + \Bigl(\tfrac14 - \nu^{2} + 2\pi k\,y - 4\pi^{2} y^{2}\Bigr) f(y) = 0,$$
--   the coefficients being read in $\mathbb{C}$ via the coercions of $y$, $k$ and $\pi$. The conclusion asserts the existence of a real number $\delta$ with $\delta > 0$ and of a real constant $C$ (no positivity of $C$ is asserted) such that $\lVert f(y)\rVert \le C\, y^{\delta}$ for every real $y$ with $0 < y \le 1$, the power $y^{\delta}$ being the real power function. Thus some positive power bound holds near the origin, with no specific exponent claimed and with no hypothesis imposed on the behaviour of $f$ at infinity.
--
--   This is the elementary local statement that at the regular singular point $y = 0$ of the Whittaker-type equation, whose indicial exponents are $\tfrac12 \pm \nu$, every solution is dominated by a positive power of $y$ once $|\mathrm{Re}\,\nu| < 1/2$. It is used in the analysis of Whittaker coefficients of automorphic forms, in the results bounding $\lVert$Whittaker coefficient at the identity diagonal element$\rVert$ by a power of the idele norm under the trichotomy for the Casimir eigenvalue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half
    (ν : ℂ) (hre : |ν.re| < 1 / 2) (k : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ δ := by sorry
