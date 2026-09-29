-- Prove2me | Theorems.Thm_LanglandsTunnell_linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth
-- name    : LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/3fb0208e-6657-58e8-8194-39210c9fe5bf
-- title:
--   Moderate-growth Whittaker solution strings on GL₂(ℂ) are proportional
-- statement:
--   Fix a natural number $n$, complex numbers $\kappa,\lambda,\lambda'$ with $\kappa\neq 0$, and two families $f,g:\mathbb{N}\to\mathbb{R}\to\mathbb{C}$ of complex-valued functions of a real variable. Assume that for each index $p\in\{0,\dots,n\}$ the function $f_p$ is differentiable on $(0,\infty)$, its derivative is again differentiable on $(0,\infty)$, and for every $y>0$, writing $q=n-2p$, the two relations $$y^2 f_p''(y)+(q-1)\,y f_p'(y)+\Bigl(\tfrac{q(q-4)}{4}+4\lambda-16\pi^2\|\kappa\|^2 y^2\Bigr) f_p(y)+8\pi i\,\kappa\, y\, f_{p+1}(y)=0,$$ $$y^2 f_p''(y)-(q+1)\,y f_p'(y)+\Bigl(\tfrac{q(q+4)}{4}+4\lambda'-16\pi^2\|\kappa\|^2 y^2\Bigr) f_p(y)-8\pi i\,\bar\kappa\, p(n+1-p)\, y\, f_{p-1}(y)=0$$ hold, the index $p-1$ being truncated natural subtraction (harmless, since the term carries the factor $p$); and assume the same for $g$, with the same $n$, $\kappa$, $\lambda$, $\lambda'$. Assume further that the bottom members have moderate growth: there are $C,N\in\mathbb{R}$ with $\|f_0(y)\|\le C y^{N}$ for all $y\ge 1$, and similarly for $g_0$. Then there exists a pair $(c_1,c_2)\in\mathbb{C}^2$, not equal to $0$, with $c_1 f_p(y)+c_2 g_p(y)=0$ for every $p\in\{0,\dots,n\}$ and every $y>0$. Members $f_p,g_p$ with $p>n$ are unconstrained.
--
--   The displayed system is the Iwasawa-coordinate form of the pair of Casimir relations satisfied by the circle-weight components of a single $SU(2)$-type of a Whittaker function on $\mathrm{GL}_2(\mathbb{C})$, and the result is the corresponding uniqueness statement: a string of such components with moderate growth in its bottom member is determined up to a scalar. It feeds the computation of Whittaker coefficients at the identity for automorphic forms at a complex place, via the uniqueness of moderate-growth solutions of Whittaker's equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (f g : ℕ → ℝ → ℂ)
    (hf : ∀ p : Fin (n + 1),
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
    (hg : ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (g p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (g p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (g p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (g p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * g p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * g ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (g p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (g p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * g p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              g ((p : ℕ) - 1) y = 0))
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f 0 y‖ ≤ C * y ^ N)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g 0 y‖ ≤ C * y ^ N) :
    ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ p : Fin (n + 1), ∀ y : ℝ, 0 < y → c.1 * f p y + c.2 * g p y = 0 := by sorry
