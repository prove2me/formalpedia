-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos
-- name    : LanglandsTunnell.exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/e39a5303-e9ad-5e86-a59d-8a528e9aceed
-- title:
--   Uniform decay near 0 for an SU(2)-string Whittaker system
-- statement:
--   Fix a natural number $n$ and complex numbers $\kappa,\lambda,\lambda'$ with $\kappa\neq 0$, $\lambda'=\lambda$, $\operatorname{Im}\lambda=0$ and $\operatorname{Re}\lambda>0$, and let $f:\mathbb{N}\to\mathbb{R}\to\mathbb{C}$ be a family of functions. Assume that for every index $p\in\{0,\dots,n\}$ the function $f_p$ and its derivative are differentiable on $(0,\infty)$, and that, writing $q=n-2p$, the two equations
--   $$y^2f_p''(y)+(q-1)\,y\,f_p'(y)+\Bigl(\tfrac{q(q-4)}{4}+4\lambda-16\pi^2\lVert\kappa\rVert^2y^2\Bigr)f_p(y)+8\pi i\,\kappa\,y\,f_{p+1}(y)=0,$$
--   $$y^2f_p''(y)-(q+1)\,y\,f_p'(y)+\Bigl(\tfrac{q(q+4)}{4}+4\lambda'-16\pi^2\lVert\kappa\rVert^2y^2\Bigr)f_p(y)-8\pi i\,\bar\kappa\,p(n+1-p)\,y\,f_{p-1}(y)=0$$
--   hold for all real $y>0$ (the index $p-1$ being truncated subtraction in $\mathbb{N}$, harmless since its coefficient vanishes at $p=0$). Assume further that $f_{n+1}$ vanishes identically on $\mathbb{R}$. Then there exist a real $\delta>0$ and a real constant $C$ such that $\lVert f_p(y)\rVert\le C\,y^{\delta}$ (real power) for every $p\in\{0,\dots,n\}$ and every $y$ with $0<y\le 1$. The exponent $\delta$ is asserted to exist, with no explicit value, and $C$ is not required to be positive.
--
--   This is the decay near the cusp-end $y\to 0^+$ of the torus Whittaker functions attached to an $SU(2)$-string at a complex place, in the case where the two Casimir scalars agree and are real and positive, so that the associated Whittaker parameter satisfies $|\operatorname{Re}\nu|<1$. It feeds the estimate on Whittaker coefficients at a complex place used in the Langlands–Tunnell argument, via the two Whittaker-type second-order estimates [`LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode`](thm.html#LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode) and [`LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing`](thm.html#LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (hlam' : lam' = lam) (hreal : lam.im = 0) (hpos : 0 < lam.re) (f : ℕ → ℝ → ℂ)
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0))
    (hfn : ∀ y : ℝ, f (n + 1) y = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ δ := by sorry
