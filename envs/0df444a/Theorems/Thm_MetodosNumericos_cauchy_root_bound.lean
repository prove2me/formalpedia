-- Prove2me | Theorems.Thm_MetodosNumericos_cauchy_root_bound
-- name    : MetodosNumericos.cauchy_root_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:35:57.46319+00:00
-- url     : https://prove2.me/theorems/65d16c25-860d-4a61-84fd-9fdbb3d3d764
-- title:
--   All roots lie in the circle of radius $1 + A/|a_0|$
-- statement:
--   Let $P(z) = a_0z^n + a_1z^{n-1} + \\dots + a_n$ have real coefficients with $a_0 \\neq 0$ and $n \\ge 1$, and let $A = \\max\\{|a_1|, \\dots, |a_n|\\}$. Then every complex root of $P$ satisfies $|z| \\le 1 + A/|a_0|$. This is Proposição 4.2.1, the localization result the chapter uses to bound the search region for the zeros of a polynomial.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 4, Proposição 4.2.1, p. 74.

import Mathlib
import Definitions.Def_MetodosNumericos_polinomiosDefs

namespace MetodosNumericos

theorem cauchy_root_bound (a : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (ha0 : a 0 ≠ 0)
    (A : ℝ) (hA : A = Finset.sup' (Finset.Icc 1 n) (by simp [Finset.nonempty_Icc, hn])
      (fun i => |a i|))
    (z : ℂ) (hz : polyValC a n z = 0) :
    ‖z‖ ≤ 1 + A / |a 0| := by sorry

end MetodosNumericos
