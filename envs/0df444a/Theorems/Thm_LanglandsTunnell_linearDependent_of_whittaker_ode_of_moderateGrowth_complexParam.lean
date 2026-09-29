-- Prove2me | Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
-- name    : LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/889ce0d2-5d15-5c2a-8a8b-075b46af6e85
-- title:
--   Moderate-growth solutions of the Whittaker equation are dependent
-- statement:
--   Let $\nu$ be a complex number, $k$ a real number, and let $f, g \colon \mathbb{R} \to \mathbb{C}$ be functions. Assume that $f$ is differentiable on $(0,\infty)$, that its derivative is again differentiable on $(0,\infty)$, and that for every $y > 0$ one has $y^{2} f''(y) + \bigl(\tfrac14 - \nu^{2} + 2\pi k y - 4\pi^{2} y^{2}\bigr) f(y) = 0$, the coefficients being read in $\mathbb{C}$ and the derivatives being the iterated real derivatives of $f$; assume moreover that $f$ has moderate growth at infinity in the sense that there exist real constants $C$ and $N$ with $\lVert f(y)\rVert \le C y^{N}$ (real power) for all $y \ge 1$. Assume the same four hypotheses for $g$, with the same $\nu$ and $k$. Then $f$ and $g$ are linearly dependent on the positive half-line: there exist $c_1, c_2 \in \mathbb{C}$ with $(c_1, c_2) \neq (0,0)$ such that $c_1 f(y) + c_2 g(y) = 0$ for every $y > 0$. No hypothesis is imposed on the values of $f$ and $g$ outside $(0,\infty)$.
--
--   This is the uniqueness statement for archimedean Whittaker functions in the normalisation used for weight-$k$ forms: the second-order equation has a two-dimensional solution space on $(0,\infty)$, and the condition of moderate growth cuts out at most a line in it, since for large $y$ the term $-4\pi^{2} y^{2}$ dominates and forces exponential decay. It is used in the analysis of Whittaker coefficients of cusp forms that are Casimir eigenvectors, and in the archimedean computations of the converse-theorem input, where it identifies a Whittaker function up to a scalar from its differential equation and growth alone.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam (ν : ℂ)
    (k : ℝ) (f g : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hg : DifferentiableOn ℝ g (Set.Ioi 0)) (hg' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv g) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y ^ N) :
    ∃ c₁ c₂ : ℂ, (c₁, c₂) ≠ 0 ∧ ∀ y : ℝ, 0 < y → c₁ * f y + c₂ * g y = 0 := by sorry
