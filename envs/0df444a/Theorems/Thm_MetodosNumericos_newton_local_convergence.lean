-- Prove2me | Theorems.Thm_MetodosNumericos_newton_local_convergence
-- name    : MetodosNumericos.newton_local_convergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:18:25.891984+00:00
-- url     : https://prove2.me/theorems/8d37de77-1c80-43b3-bc91-a938fb9815ed
-- title:
--   Local convergence of Newton's method
-- statement:
--   Let $f$ be twice differentiable on an open interval $(a,b)$, with continuous second derivative and with $f'$ nowhere zero on $(a,b)$, and let $\\bar{x} \\in (a,b)$ satisfy $f(\\bar{x}) = 0$. Then there exists $h > 0$ such that $[\\bar{x}-h, \\bar{x}+h] \\subseteq (a,b)$ and, for every starting point $x_0$ in that closed neighbourhood, the Newton sequence $x_{n+1} = x_n - f(x_n)/f'(x_n)$ converges to $\\bar{x}$. This is the conclusion the source draws from Proposição 3.5.1: once the initial guess is close enough to the root, Newton's method converges.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 3, Proposição 3.5.1 and the ATENÇÃO following it, pp. 61–62.

import Mathlib
import Definitions.Def_MetodosNumericos_zerosDefs

open Filter Topology

namespace MetodosNumericos

theorem newton_local_convergence (f f' f'' : ℝ → ℝ) (a b xbar : ℝ)
    (hxbar : xbar ∈ Set.Ioo a b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x)
    (hf'' : ContinuousOn f'' (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, f' x ≠ 0)
    (hroot : f xbar = 0) :
    ∃ h > 0, Set.Icc (xbar - h) (xbar + h) ⊆ Set.Ioo a b ∧
      ∀ x0 ∈ Set.Icc (xbar - h) (xbar + h),
        Tendsto (newtonSeq f f' x0) atTop (𝓝 xbar) := by sorry

end MetodosNumericos
