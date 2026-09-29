-- Prove2me | Theorems.Thm_MetodosNumericos_euler_local_error
-- name    : MetodosNumericos.euler_local_error
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:53:54.507165+00:00
-- url     : https://prove2.me/theorems/a2dac270-083a-4bc2-9911-6a8254be1955
-- title:
--   One-step Taylor identity behind Euler's method
-- statement:
--   If $\\varphi$ solves $y'=f(x,y)$ on $[x, x+h]$ and is twice continuously differentiable there, then there is $\\mu \\in (x, x+h)$ with $$\\varphi(x+h) = \\varphi(x) + h f(x,\\varphi(x)) + \\frac{h^2}{2}\\varphi''(\\mu),$$ which exhibits the local error of one Euler step as $O(h^2)$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 9, §9.9, p. 192 (Taylor expansion preceding the Euler algorithm).

import Mathlib

namespace MetodosNumericos

theorem euler_local_error (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x h : ℝ) (hh : 0 < h)
    (hsol : ∀ t ∈ Set.Icc x (x + h), HasDerivAt phi (f t (phi t)) t)
    (hphi2 : ContDiffOn ℝ 2 phi (Set.Icc x (x + h))) :
    ∃ mu ∈ Set.Ioo x (x + h),
      phi (x + h) =
        phi x + h * f x (phi x) + h ^ 2 / 2 * iteratedDerivWithin 2 phi (Set.Icc x (x + h)) mu := by
  sorry

end MetodosNumericos
