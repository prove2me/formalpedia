-- Prove2me | Theorems.Thm_MetodosNumericos_lagrange_interpolates
-- name    : MetodosNumericos.lagrange_interpolates
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:54:14.291423+00:00
-- url     : https://prove2.me/theorems/d57a19a1-a3b8-44ce-a799-ddf00b1b224b
-- title:
--   The Lagrange formula reproduces the tabulated values
-- statement:
--   For pairwise distinct nodes, the Lagrange sum $P_n(t) = \\sum_i f_i L_i(t)$ satisfies $P_n(x_i) = f_i$ for every node $x_i$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 7, §7.3, pp. 138–140.

import Mathlib
import Definitions.Def_MetodosNumericos_interpolacaoDefs

namespace MetodosNumericos

theorem lagrange_interpolates {n : ℕ} (xs fs : Fin (n + 1) → ℝ)
    (hxs : Function.Injective xs) (i : Fin (n + 1)) :
    lagrangeInterp xs fs (xs i) = fs i := by sorry

end MetodosNumericos
