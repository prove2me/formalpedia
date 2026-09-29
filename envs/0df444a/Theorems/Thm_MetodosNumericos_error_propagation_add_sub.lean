-- Prove2me | Theorems.Thm_MetodosNumericos_error_propagation_add_sub
-- name    : MetodosNumericos.error_propagation_add_sub
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:39:54.20598+00:00
-- url     : https://prove2.me/theorems/6719e39e-c2b3-40ec-b3e7-6057018630a3
-- title:
--   Propagation of absolute errors under addition and subtraction
-- statement:
--   With $e_x = x - \\tilde{x}$ and $e_y = y - \\tilde{y}$, the errors of the sum and the difference are $e_{x+y} = e_x + e_y$ and $e_{x-y} = e_x - e_y$. These are items 1 and 2 of §2.5.1.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 2, §2.5.1 items 1–2, p. 25.

import Mathlib

namespace MetodosNumericos

theorem error_propagation_add_sub (x y xt yt : ℝ) :
    (x + y) - (xt + yt) = (x - xt) + (y - yt) ∧
      (x - y) - (xt - yt) = (x - xt) - (y - yt) := by sorry

end MetodosNumericos
