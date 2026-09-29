-- Prove2me | Theorems.Thm_MetodosNumericos_mil_convergence
-- name    : MetodosNumericos.mil_convergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:00:20.168459+00:00
-- url     : https://prove2.me/theorems/fadc21ce-b079-4286-9b22-0b78e105f0aa
-- title:
--   Convergence of the linear iterative method under $|g'| \\le L < 1$
-- statement:
--   Let $g$ be differentiable on $[a,b]$ with derivative $g'$, let $|g'(x)| \\le L$ for all $x \\in [a,b]$ with $L < 1$, and assume $g$ maps $[a,b]$ into itself. If $\\bar{x} \\in [a,b]$ is a fixed point of $g$ and $x_0 \\in [a,b]$, then the iterates $x_{n+1} = g(x_n)$ converge to $\\bar{x}$. This is item (i) of Proposição 3.3.2, with the invariance of the interval added as an explicit hypothesis.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 3, Proposição 3.3.2 (i), pp. 46–47.

import Mathlib
import Definitions.Def_MetodosNumericos_zerosDefs

open Filter Topology

namespace MetodosNumericos

theorem mil_convergence (g g' : ℝ → ℝ) (a b L x0 xbar : ℝ)
    (hmaps : ∀ x ∈ Set.Icc a b, g x ∈ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Set.Icc a b, |g' x| ≤ L) (hL : L < 1)
    (hx0 : x0 ∈ Set.Icc a b) (hxbar : xbar ∈ Set.Icc a b) (hfix : g xbar = xbar) :
    Tendsto (iterSeq g x0) atTop (𝓝 xbar) := by sorry

end MetodosNumericos
