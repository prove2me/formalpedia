-- Prove2me | Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag
-- name    : LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/449b273e-744f-5397-ac37-36be918afbac
-- title:
--   Decay at a regular singular point for a diagonal first-order system
-- statement:
--   Let $m$ be a natural number, $a : \mathrm{Fin}\,m \to \mathbb{C}$ a family of complex numbers, and $r_0, c, \tau$ real numbers with $\tau > 0$ and $r_0 \le \operatorname{Re} a_i$ for every index $i$. Let $B$ assign to each real $y$ a complex $m \times m$ matrix, subject to the entrywise bound $\|B(y)_{ij}\| \le c\,y^{\tau}$ (real power) for all $0 < y \le 1$ and all $i, j$. Let $F_i : \mathbb{R} \to \mathbb{C}$, for $i$ in $\mathrm{Fin}\,m$, be functions each of which is differentiable on the open half-line $(0,\infty)$ (as a function of a real variable), and assume that for every $y$ with $0 < y \le 1$ and every $i$ the system
--   $$y\,F_i'(y) = a_i F_i(y) + \sum_j B(y)_{ij} F_j(y)$$
--   holds, the left-hand side being $y$ viewed as a complex number times the derivative of $F_i$ at $y$. The conclusion is that for every $\varepsilon > 0$ there exists a real constant $C$ such that $\|F_i(y)\| \le C\,y^{\,r_0 - \varepsilon}$ for all $0 < y \le 1$ and all $i$, the exponent again being a real power. No positivity of $C$ is asserted, and $C$ may depend on all the data, including $\varepsilon$.
--
--   This is a Grönwall-type decay estimate at a regular singular point: a first-order system whose leading matrix is the diagonal matrix $\mathrm{diag}(a_1,\dots,a_m)$ perturbed by an $O(y^{\tau})$ error has all solutions bounded by $y^{r_0 - \varepsilon}$ near $y = 0$, where $r_0$ is a lower bound for the real parts of the diagonal exponents. It is used in the analytic input to the Langlands–Tunnell argument, where it certifies simultaneous decay of the components of a system coming from the Casimir equations on a torus (see [`LanglandsTunnell.norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq`](thm.html#LanglandsTunnell.norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_system_of_diag.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag
    (m : ℕ) (a : Fin m → ℂ) (r₀ c τ : ℝ) (hτ : 0 < τ) (ha : ∀ i, r₀ ≤ (a i).re)
    (B : ℝ → Matrix (Fin m) (Fin m) ℂ) (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j, ‖B y i j‖ ≤ c * y ^ τ)
    (F : Fin m → ℝ → ℂ) (hF : ∀ i, DifferentiableOn ℝ (F i) (Set.Ioi 0))
    (hFeq : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i,
      (y : ℂ) * deriv (F i) y = a i * F i y + ∑ j, B y i j * F j y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, ‖F i y‖ ≤ C * y ^ (r₀ - ε) := by sorry
