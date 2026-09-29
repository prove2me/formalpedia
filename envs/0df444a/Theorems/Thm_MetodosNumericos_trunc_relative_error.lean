-- Prove2me | Theorems.Thm_MetodosNumericos_trunc_relative_error
-- name    : MetodosNumericos.trunc_relative_error
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:37:59.768178+00:00
-- url     : https://prove2.me/theorems/9623a1d4-598a-4197-b952-2cbd6d9278e6
-- title:
--   Relative error of truncated rounding is below $10^{1-t}$
-- statement:
--   For $x>0$ and $t \\ge 1$, truncated rounding to $t$ digits satisfies $|x-\\tilde{x}|/|\\tilde{x}| < 10^{1-t}$. This is Proposição 2.4.2.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 2, Proposição 2.4.2, p. 24.

import Mathlib
import Definitions.Def_MetodosNumericos_errosDefs

namespace MetodosNumericos

theorem trunc_relative_error (t : ℕ) (ht : 1 ≤ t) (x : ℝ) (hx : 0 < x) :
    |x - truncRound t x| / |truncRound t x| < (10 : ℝ) ^ (1 - (t : ℤ)) := by sorry

end MetodosNumericos
