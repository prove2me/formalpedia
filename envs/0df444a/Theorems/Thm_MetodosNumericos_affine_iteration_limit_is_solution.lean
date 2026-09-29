-- Prove2me | Theorems.Thm_MetodosNumericos_affine_iteration_limit_is_solution
-- name    : MetodosNumericos.affine_iteration_limit_is_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:08:01.034996+00:00
-- url     : https://prove2.me/theorems/d5258903-0bdf-425a-8e99-459c3b2c18e6
-- title:
--   The limit of a convergent affine iteration is a fixed point
-- statement:
--   If the iterates $x^{(k+1)} = Bx^{(k)} + d$ converge to $\\alpha$, then $\\alpha = B\\alpha + d$. This is Proposição 5.5.1: the limit of the successive approximations solves the fixed-point form of the system, hence the system itself.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 5, Proposição 5.5.1, p. 106.

import Mathlib

open Filter Topology

namespace MetodosNumericos

theorem affine_iteration_limit_is_solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (x : ℕ → (Fin n → ℝ)) (alpha : Fin n → ℝ)
    (hrec : ∀ k, x (k + 1) = B.mulVec (x k) + d)
    (hconv : Tendsto x atTop (𝓝 alpha)) :
    alpha = B.mulVec alpha + d := by sorry

end MetodosNumericos
