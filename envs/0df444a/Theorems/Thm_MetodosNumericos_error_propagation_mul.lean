-- Prove2me | Theorems.Thm_MetodosNumericos_error_propagation_mul
-- name    : MetodosNumericos.error_propagation_mul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:40:11.48998+00:00
-- url     : https://prove2.me/theorems/a33b4c6d-bf01-4fa0-95b4-b74a47727348
-- title:
--   Propagation of absolute errors under multiplication
-- statement:
--   With $e_x = x-\\tilde{x}$ and $e_y = y-\\tilde{y}$, the exact error of the product is $e_{xy} = \\tilde{x}e_y + \\tilde{y}e_x + e_xe_y$. The source states the first-order approximation $e_{xy} \\approx \\tilde{x}e_y + \\tilde{y}e_x$, obtained by neglecting the second-order term; the milestone asks for the identity that includes it.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 2, §2.5.1 item 3, eq. (2.10), p. 25.

import Mathlib

namespace MetodosNumericos

theorem error_propagation_mul (x y xt yt : ℝ) :
    x * y - xt * yt = xt * (y - yt) + yt * (x - xt) + (x - xt) * (y - yt) := by sorry

end MetodosNumericos
