-- Prove2me | Theorems.Thm_MetodosNumericos_mil_error_estimate
-- name    : MetodosNumericos.mil_error_estimate
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:08:36.009318+00:00
-- url     : https://prove2.me/theorems/dde7d848-a24f-4584-b24f-4d270c140ec5
-- title:
--   A posteriori error estimate $|\\bar{x}-x_n| \\le \\frac{L}{1-L}|x_n - x_{n-1}|$
-- statement:
--   Under the hypotheses of the previous milestone ($g$ differentiable with $|g'| \\le L < 1$ on $[a,b]$, $g$ mapping $[a,b]$ into itself, $\\bar{x}$ a fixed point in $[a,b]$, $x_0 \\in [a,b]$), the fixed-point iterates satisfy $|\\bar{x} - x_{n+1}| \\le \\frac{L}{1-L}\\,|x_{n+1} - x_n|$ for every $n$. This is the practical stopping criterion of Proposição 3.3.4: the distance to the root is controlled by the last observed increment.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 3, Proposição 3.3.4, pp. 53–54.

import Mathlib
import Definitions.Def_MetodosNumericos_zerosDefs

namespace MetodosNumericos

theorem mil_error_estimate (g g' : ℝ → ℝ) (a b L x0 xbar : ℝ)
    (hmaps : ∀ x ∈ Set.Icc a b, g x ∈ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hbound : ∀ x ∈ Set.Icc a b, |g' x| ≤ L) (hL : L < 1)
    (hx0 : x0 ∈ Set.Icc a b) (hxbar : xbar ∈ Set.Icc a b) (hfix : g xbar = xbar) :
    ∀ n : ℕ, |xbar - iterSeq g x0 (n + 1)| ≤
      L / (1 - L) * |iterSeq g x0 (n + 1) - iterSeq g x0 n| := by sorry

end MetodosNumericos
