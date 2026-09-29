-- Prove2me | Theorems.Thm_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer
-- name    : LanglandsTunnell.whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/25a2376c-17c6-5f3f-ac56-ef006d3e6555
-- title:
--   Behaviour at 0 of solutions of Whittaker's equation, half-integral ν
-- statement:
--   Fix a natural number $n \ge 1$, a complex number $\nu$ with $\nu = n/2$, a real number $\kappa$, and a function $f \colon \mathbb{R} \to \mathbb{C}$ such that $f$ and its derivative $\operatorname{deriv} f$ are both differentiable on the open half-line $(0,\infty)$, and such that for every real $y > 0$ one has the Whittaker-type equation $y^2 f''(y) + \bigl(\tfrac14 - \nu^2 + 2\pi\kappa y - 4\pi^2 y^2\bigr) f(y) = 0$ (the coefficients and $y$ being read in $\mathbb{C}$, and $f''$ meaning $\operatorname{deriv}(\operatorname{deriv} f)$). Then there exist $c \in \mathbb{C}$ and a real $\delta > 0$ with the following two properties. First, for some real constant $C$ and all $y$ with $0 < y \le 1$, $\bigl\| f(y) - c\, y^{1/2-\nu} \bigr\| \le C\, y^{1/2 - n/2 + \delta}$, the power $y^{1/2-\nu}$ being the complex power and $y^{1/2-n/2+\delta}$ the real power. Second, if $c = 0$ then: the function $y \mapsto y^{-(1/2+\nu)} f(y)$ tends to a finite limit $L \in \mathbb{C}$ as $y \to 0^+$; the function $y \mapsto y^{1/2-\nu}\bigl(f'(y) - \tfrac{1/2+\nu}{y} f(y)\bigr)$ tends to $0$ as $y \to 0^+$; and for some real constant $C'$ and all $0 < y \le 1$, $\|f(y)\| \le C'\, y^{1/2 + n/2}$. Only a gain of an unspecified $\delta > 0$ in the exponent of the error term is asserted, rather than the full gain of one power of $y$ that the equation would give.
--
--   This is the analysis of the regular singular point $y = 0$ of Whittaker's equation in the resonant case where the two exponents $\tfrac12 \pm \nu$ differ by the positive integer $n$: it isolates the coefficient $c$ of the dominant solution $y^{1/2-\nu}$ and, when that coefficient vanishes, records the recessive behaviour $O(y^{1/2+n/2})$ together with the associated limits. It is used in the proof of [`LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul`](thm.html#LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul), and rests on the a priori bound [`LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode`](thm.html#LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Real Complex Filter Topology

theorem LanglandsTunnell.whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer
    (n : ℕ) (hn : 1 ≤ n) (ν : ℂ) (hν : ν = (n : ℂ) / 2) (κ : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ (c : ℂ) (δ : ℝ), 0 < δ ∧
      (∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖f y - c * (y : ℂ) ^ (1 / 2 - ν)‖ ≤ C * y ^ (1 / 2 - (n : ℝ) / 2 + δ)) ∧
      (c = 0 →
        (∃ L : ℂ, Tendsto (fun y : ℝ => (y : ℂ) ^ (-(1 / 2 + ν)) * f y) (𝓝[>] 0) (𝓝 L)) ∧
        Tendsto (fun y : ℝ => (y : ℂ) ^ (1 / 2 - ν) * (deriv f y - (1 / 2 + ν) / (y : ℂ) * f y)) (𝓝[>] 0) (𝓝 0) ∧
        ∃ C' : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C' * y ^ (1 / 2 + (n : ℝ) / 2)) := by sorry
