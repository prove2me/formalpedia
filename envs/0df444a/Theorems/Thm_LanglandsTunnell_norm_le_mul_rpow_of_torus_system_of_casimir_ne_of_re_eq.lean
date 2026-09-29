-- Prove2me | Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq
-- name    : LanglandsTunnell.norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/fee5dc49-340c-5dfa-a89a-d6916e84b3d0
-- title:
--   Decay O(y^{1-ε}) for a complex-place torus Whittaker system
-- statement:
--   Fix $n\in\mathbb{N}$ and $\kappa,\lambda,\lambda'\in\mathbb{C}$ with $\kappa\neq 0$, with $\operatorname{Re}\lambda=\operatorname{Re}\lambda'$, and such that either $\lambda\neq\lambda'$ or $n$ is odd. Let $f:\mathbb{N}\to\mathbb{R}\to\mathbb{C}$ be a family of functions with $f_{n+1}$ identically zero, and suppose that for every index $p\in\{0,\dots,n\}$ the function $f_p$ and its derivative are both differentiable on $(0,\infty)$ and, writing $q=n-2p$, that for all $y>0$ the two equations
--   $$y^2f_p''(y)+(q-1)y f_p'(y)+\Bigl(\tfrac{q(q-4)}{4}+4\lambda-16\pi^2\|\kappa\|^2y^2\Bigr)f_p(y)+8\pi i\,\kappa\, y\, f_{p+1}(y)=0,$$
--   $$y^2f_p''(y)-(q+1)y f_p'(y)+\Bigl(\tfrac{q(q+4)}{4}+4\lambda'-16\pi^2\|\kappa\|^2y^2\Bigr)f_p(y)-8\pi i\,\bar\kappa\, p(n+1-p)\, y\, f_{p-1}(y)=0$$
--   hold, where the index $p-1$ is truncated natural subtraction (harmless, since its coefficient vanishes at $p=0$). The conclusion is that for every $\varepsilon>0$ there is a constant $C\in\mathbb{R}$ such that $\|f_p(y)\|\le C\,y^{1-\varepsilon}$ for all $p\in\{0,\dots,n\}$ and all $y$ with $0<y\le 1$, the power being the real power function.
--
--   This is the near-zero decay estimate for the system of functions on the diagonal torus attached to an $SU(2)$-string of Whittaker coefficients at a complex place, in the case where the two Casimir scalars have equal real parts and are distinct, or the string has odd length. It is obtained from the estimate for regular singular first-order systems with diagonal leading term [`LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag`](thm.html#LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag), and feeds the bound on Whittaker coefficients of $K$-finite vectors at a complex place used in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (hne : lam ≠ lam' ∨ Odd n) (hre : lam.re = lam'.re) (f : ℕ → ℝ → ℂ)
    (hfn : ∀ y : ℝ, f (n + 1) y = 0)
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
              f ((p : ℕ) - 1) y = 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ (1 - ε) := by sorry
