-- Prove2me | Theorems.Thm_MetodosNumericos_root_lower_bound
-- name    : MetodosNumericos.root_lower_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:35:35.78868+00:00
-- url     : https://prove2.me/theorems/99a60568-2bf0-4659-bae1-47122ff74c4e
-- title:
--   Roots lie outside the circle of radius $1/(1 + B/|a_n|)$
-- statement:
--   Let $P(z) = a_0z^n + \\dots + a_n$ have real coefficients with $a_n \\neq 0$ and $n \\ge 1$, and put $B = \\max\\{|a_0|, \\dots, |a_{n-1}|\\}$. Then every complex root satisfies $|z| \\ge 1/(1 + B/|a_n|)$. This is Proposição 4.2.2, obtained in the source from the outer bound applied to the reversed polynomial.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 4, Proposição 4.2.2, p. 75.

import Mathlib
import Definitions.Def_MetodosNumericos_polinomiosDefs

namespace MetodosNumericos

theorem root_lower_bound (a : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (han : a n ≠ 0)
    (B : ℝ) (hB : B = Finset.sup' (Finset.range n) (by simp [Finset.nonempty_range_iff]; omega)
      (fun i => |a i|))
    (z : ℂ) (hz : polyValC a n z = 0) :
    1 / (1 + B / |a n|) ≤ ‖z‖ := by sorry

end MetodosNumericos
