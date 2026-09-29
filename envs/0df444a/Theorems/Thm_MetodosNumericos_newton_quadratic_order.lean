-- Prove2me | Theorems.Thm_MetodosNumericos_newton_quadratic_order
-- name    : MetodosNumericos.newton_quadratic_order
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:15:53.406557+00:00
-- url     : https://prove2.me/theorems/81700ddc-c0f0-47ca-848e-378ae9b002cd
-- title:
--   Newton's method has order of convergence 2 at a simple zero
-- statement:
--   Let $f$ be twice differentiable on $(a,b)$ with continuous second derivative, $f' \\neq 0$ on $(a,b)$, and let $\\bar{x} \\in (a,b)$ be a zero of $f$. If the Newton iterates from $x_0$ stay in $(a,b)$, are never equal to $\\bar{x}$, and converge to $\\bar{x}$, then $$\\frac{|x_{n+1}-\\bar{x}|}{|x_n-\\bar{x}|^2} \\longrightarrow \\frac{|f''(\\bar{x})|}{2|f'(\\bar{x})|},$$ i.e. the convergence is quadratic. This is item (i) of Proposição 3.5.2, the case of a zero of order $m=1$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 3, Proposição 3.5.2 (i), p. 64.

import Mathlib
import Definitions.Def_MetodosNumericos_zerosDefs

open Filter Topology

namespace MetodosNumericos

theorem newton_quadratic_order (f f' f'' : ℝ → ℝ) (a b xbar x0 : ℝ)
    (hxbar : xbar ∈ Set.Ioo a b)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Ioo a b, HasDerivAt f' (f'' x) x)
    (hf'' : ContinuousOn f'' (Set.Ioo a b))
    (hne : ∀ x ∈ Set.Ioo a b, f' x ≠ 0)
    (hroot : f xbar = 0)
    (hmem : ∀ n : ℕ, newtonSeq f f' x0 n ∈ Set.Ioo a b)
    (hsimple : ∀ n : ℕ, newtonSeq f f' x0 n ≠ xbar)
    (hconv : Tendsto (newtonSeq f f' x0) atTop (𝓝 xbar)) :
    Tendsto (fun n : ℕ =>
        |newtonSeq f f' x0 (n + 1) - xbar| / |newtonSeq f f' x0 n - xbar| ^ 2)
      atTop (𝓝 (|f'' xbar| / (2 * |f' xbar|))) := by sorry

end MetodosNumericos
