-- Prove2me | Theorems.Thm_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul
-- name    : LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/44e6b237-bbe7-5a2f-944e-a0d29a455ad4
-- title:
--   Vanishing of moderate-growth Whittaker solutions of wrong sign
-- statement:
--   Let $n$ be a natural number and $\nu$ a complex number with $\nu = n/2$, let $k$ be a real number with $k > 0$, and let $f \colon \mathbb{R} \to \mathbb{C}$ be differentiable on $(0,\infty)$ with $f'$ again differentiable on $(0,\infty)$, and suppose that for every $y > 0$
--   $$y^2 f''(y) + \Bigl(\tfrac14 - \nu^2 - 2\pi k\, y - 4\pi^2 y^2\Bigr) f(y) = 0,$$
--   that is, the Whittaker equation with the parameter $2\pi\kappa$ taken at $\kappa = -k < 0$. Assume $f$ has moderate growth at infinity: there are real $C, N$ with $\lVert f(y)\rVert \le C y^{N}$ for all $y \ge 1$. Assume further that there is a real number $\sigma_0$ and an entire function $\Psi \colon \mathbb{C} \to \mathbb{C}$ such that for every $s$ with $\operatorname{Re} s > \sigma_0$ the Mellin integral of $f$ at $s$ converges in the sense of `MellinConvergent` and $\operatorname{mellin} f\,(s) = \Gamma_{\mathbb{C}}\bigl(s + \tfrac12 + \nu\bigr)\,\Psi(s)$. Then $f(y) = 0$ for every $y > 0$.
--
--   The archimedean rigidity step in the converse-theorem input to Langlands–Tunnell: a Whittaker-type solution with the sign of the linear term opposite to the one giving exponential decay, yet of moderate growth and with Mellin transform divisible by the expected archimedean $\Gamma$-factor, must vanish identically. It is invoked in the treatment of the archimedean datum for representations of negative determinant sign, both in the discrete-series and in the principal-series cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Real Complex

theorem LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul
    (n : ℕ) (ν : ℂ) (hν : ν = (n : ℂ) / 2) (k : ℝ) (hk : 0 < k) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((-k : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (σ₀ : ℝ) (Ψ : ℂ → ℂ) (hΨ : Differentiable ℂ Ψ)
    (hmel : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent (fun y : ℝ => f y) s ∧ mellin (fun y : ℝ => f y) s = Complex.Gammaℂ (s + 1 / 2 + ν) * Ψ s)
    (y : ℝ) (hy : 0 < y) :
    f y = 0 := by sorry
