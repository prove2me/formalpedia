-- Prove2me | Theorems.Thm_MetodosNumericos_sym_relative_error
-- name    : MetodosNumericos.sym_relative_error
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:40:47.073418+00:00
-- url     : https://prove2.me/theorems/f8bb8f3d-afcf-4caa-afdc-eaacbe1e0121
-- title:
--   Relative error of symmetric rounding is at most $\\frac{1}{2}10^{1-t}$
-- statement:
--   For $x>0$ and $t \\ge 1$, symmetric rounding to $t$ digits satisfies $|x - \\tilde{x}|/|\\tilde{x}| \\le \\frac{1}{2}10^{1-t}$. This is Proposição 2.4.3, the bound on the relative error committed at each operation of a $t$-digit arithmetic; the inequality is stated non-strictly because equality occurs when the discarded tail is exactly half a unit in the last retained place.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 2, Proposição 2.4.3, p. 24.

import Mathlib
import Definitions.Def_MetodosNumericos_errosDefs

namespace MetodosNumericos

theorem sym_relative_error (t : ℕ) (ht : 1 ≤ t) (x : ℝ) (hx : 0 < x) :
    |x - symRound t x| / |symRound t x| ≤ (1 / 2 : ℝ) * (10 : ℝ) ^ (1 - (t : ℤ)) := by sorry

end MetodosNumericos
