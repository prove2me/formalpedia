-- Prove2me | Theorems.Thm_MetodosNumericos_trapezoid_simple_error
-- name    : MetodosNumericos.trapezoid_simple_error
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:46:23.213857+00:00
-- url     : https://prove2.me/theorems/9edd6843-41a7-4ccb-81a6-d1b16e9fe22e
-- title:
--   Error of the trapezoidal rule on one subinterval
-- statement:
--   If $f$ is twice continuously differentiable on $[x_0, x_0+h]$ with $h>0$, then there is $\\mu \\in (x_0, x_0+h)$ with $$\\int_{x_0}^{x_0+h} f = \\frac{h}{2}\\bigl(f(x_0)+f(x_0+h)\\bigr) - \\frac{h^3}{12}f''(\\mu).$$ This is the per-subinterval error $E_i^T$ of §8.1.1.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 8, §8.1.1, p. 167.

import Mathlib

namespace MetodosNumericos

theorem trapezoid_simple_error (f : ℝ → ℝ) (x0 h : ℝ) (hh : 0 < h)
    (hf : ContDiffOn ℝ 2 f (Set.Icc x0 (x0 + h))) :
    ∃ mu ∈ Set.Ioo x0 (x0 + h),
      ∫ t in x0..(x0 + h), f t =
        h / 2 * (f x0 + f (x0 + h))
          - h ^ 3 * iteratedDerivWithin 2 f (Set.Icc x0 (x0 + h)) mu / 12 := by sorry

end MetodosNumericos
