-- Prove2me | Theorems.Thm_MetodosNumericos_trapezoid_composite_error
-- name    : MetodosNumericos.trapezoid_composite_error
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:46:55.21589+00:00
-- url     : https://prove2.me/theorems/899f91c2-4c0c-4da4-a500-a4e1b2b10fad
-- title:
--   Error of the composite trapezoidal rule
-- statement:
--   If $f$ is twice continuously differentiable on $[a,b]$, $a<b$ and $n \\ge 1$, then there is $\\mu \\in (a,b)$ with $$\\int_a^b f = T_n - \\frac{(b-a)h^2}{12}f''(\\mu), \\qquad h = \\frac{b-a}{n}.$$ This is the composite error $E_n^T$ of §8.1.1.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 8, §8.1.1, pp. 167–168.

import Mathlib
import Definitions.Def_MetodosNumericos_integracaoDefs

namespace MetodosNumericos

theorem trapezoid_composite_error (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) (hab : a < b) (hn : 0 < n)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b)) :
    ∃ mu ∈ Set.Ioo a b,
      ∫ t in a..b, f t =
        trapezoidRule f a b n
          - (b - a) * ((b - a) / n) ^ 2 * iteratedDerivWithin 2 f (Set.Icc a b) mu / 12 := by
  sorry

end MetodosNumericos
