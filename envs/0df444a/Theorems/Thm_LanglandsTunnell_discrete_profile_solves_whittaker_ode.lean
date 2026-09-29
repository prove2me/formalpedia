-- Prove2me | Theorems.Thm_LanglandsTunnell_discrete_profile_solves_whittaker_ode
-- name    : LanglandsTunnell.discrete_profile_solves_whittaker_ode
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/937b2cb3-e828-5267-9285-72eb7b440e48
-- title:
--   Discrete Whittaker profile solves the weight-(n+1) Whittaker equation
-- statement:
--   Fix a natural number $n$, a real number $k$ and a complex number $\nu$, subject to $k = n+1$ and $\nu = n/2$ (the latter in $\mathbb{C}$), and let $f : \mathbb{R} \to \mathbb{C}$ be a function for which, for every real $y$, $f(y)$ is the complex number obtained by coercing the real number $y^{1/2}\bigl(2\,y^{n/2} e^{-2\pi y}\bigr)$, the powers being real powers in the sense of `Real.rpow`. The conclusion is threefold: $f$ is differentiable on the open half-line $(0,\infty)$; the derivative function $\mathrm{deriv}\, f$ is again differentiable on $(0,\infty)$; and for every real $y > 0$ the identity $$y^2\,(\mathrm{deriv}\,(\mathrm{deriv}\, f))(y) + \Bigl(\tfrac14 - \nu^2 + 2\pi k y - 4\pi^2 y^2\Bigr) f(y) = 0$$ holds in $\mathbb{C}$, with $y$, $\pi$ and $k$ coerced into $\mathbb{C}$. Differentiability is asserted only in the `DifferentiableOn` (within-set) form, and the equation only on $y>0$; no assertion is made about the behaviour of $f$ at or below $0$.
--
--   This is the elementary verification that the lowest-weight Whittaker profile $y^{k/2}e^{-2\pi y}$ (normalised here as $y^{1/2}\cdot 2y^{n/2}e^{-2\pi y}$) of the discrete-series representation of $\mathrm{GL}_2(\mathbb{R})$ of weight $k = n+1$ satisfies the second-order Whittaker differential equation with spectral parameter $\nu = n/2$. It feeds the construction of the archimedean datum at a real place in the cubic-induction step of the Langlands–Tunnell input, being cited by the existence statements for archimedean Whittaker data in the weight-one and discrete cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_discrete_profile_solves_whittaker_ode.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.discrete_profile_solves_whittaker_ode (n : ℕ) (k : ℝ) (ν : ℂ) (hk : k = n + 1)
    (hν : ν = (n : ℂ) / 2) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = ((y ^ (1 / 2 : ℝ) * (2 * y ^ ((n : ℝ) / 2) * Real.exp (-(2 * π * y))) : ℝ) : ℂ)) :
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by sorry
