-- Prove2me | Theorems.Thm_MetodosNumericos_simpson_simple_error
-- name    : MetodosNumericos.simpson_simple_error
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:47:09.106717+00:00
-- url     : https://prove2.me/theorems/35639add-d9fa-4a57-ae1f-d9b6c6804c88
-- title:
--   Error of Simpson's rule on a pair of subintervals
-- statement:
--   If $f$ is four times continuously differentiable on $[x_0-h, x_0+h]$ with $h>0$, then there is $\\mu$ in the open interval with $$\\int_{x_0-h}^{x_0+h} f = \\frac{h}{3}\\bigl(f(x_0-h)+4f(x_0)+f(x_0+h)\\bigr) - \\frac{h^5}{90}f^{(4)}(\\mu).$$ This is the per-pair error $E_i^S$ of §8.2.1.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 8, §8.2.1, pp. 173–175.

import Mathlib

namespace MetodosNumericos

theorem simpson_simple_error (f : ℝ → ℝ) (x0 h : ℝ) (hh : 0 < h)
    (hf : ContDiffOn ℝ 4 f (Set.Icc (x0 - h) (x0 + h))) :
    ∃ mu ∈ Set.Ioo (x0 - h) (x0 + h),
      ∫ t in (x0 - h)..(x0 + h), f t =
        h / 3 * (f (x0 - h) + 4 * f x0 + f (x0 + h))
          - h ^ 5 * iteratedDerivWithin 4 f (Set.Icc (x0 - h) (x0 + h)) mu / 90 := by sorry

end MetodosNumericos
