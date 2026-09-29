-- Prove2me | Theorems.Thm_MetodosNumericos_simpson_composite_error
-- name    : MetodosNumericos.simpson_composite_error
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:47:32.305389+00:00
-- url     : https://prove2.me/theorems/db0c2d27-a474-44b5-a541-e6d327f6f860
-- title:
--   Error of the composite Simpson rule
-- statement:
--   If $f$ is four times continuously differentiable on $[a,b]$ with $a<b$, and the interval is divided into $n=2k$ subintervals with $k \\ge 1$, then there is $\\mu \\in (a,b)$ with $$\\int_a^b f = S_n - \\frac{(b-a)^5}{180\\,n^4}f^{(4)}(\\mu).$$ This is equation (8.3) of §8.2.1, the capstone error formula of the chapter.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 8, §8.2.1, eq. (8.3), p. 175.

import Mathlib
import Definitions.Def_MetodosNumericos_integracaoDefs

namespace MetodosNumericos

theorem simpson_composite_error (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) (hab : a < b) (hk : 0 < k)
    (hf : ContDiffOn ℝ 4 f (Set.Icc a b)) :
    ∃ mu ∈ Set.Ioo a b,
      ∫ t in a..b, f t =
        simpsonRule f a b k
          - (b - a) ^ 5 * iteratedDerivWithin 4 f (Set.Icc a b) mu / (180 * (2 * k : ℝ) ^ 4) := by
  sorry

end MetodosNumericos
