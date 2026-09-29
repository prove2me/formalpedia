-- Prove2me | Theorems.Thm_MetodosNumericos_error_propagation_div
-- name    : MetodosNumericos.error_propagation_div
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:40:26.813503+00:00
-- url     : https://prove2.me/theorems/986a0324-a82b-4076-bc87-107ef484fb65
-- title:
--   Propagation of absolute errors under division
-- statement:
--   For $y \\neq 0$ and $\\tilde{y} \\neq 0$, the exact error of the quotient is $$\\frac{x}{y} - \\frac{\\tilde{x}}{\\tilde{y}} = \\frac{\\tilde{y}(x-\\tilde{x}) - \\tilde{x}(y-\\tilde{y})}{y\\tilde{y}}.$$ The source derives the first-order approximation $e_x/\\tilde{y} - (\\tilde{x}/\\tilde{y}^2)e_y$ from a geometric series; the milestone asks for the identity behind it.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 2, §2.5.1 item 4, eq. (2.11), pp. 26–27.

import Mathlib

namespace MetodosNumericos

theorem error_propagation_div (x y xt yt : ℝ) (hy : y ≠ 0) (hyt : yt ≠ 0) :
    x / y - xt / yt = (yt * (x - xt) - xt * (y - yt)) / (y * yt) := by sorry

end MetodosNumericos
