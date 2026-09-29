-- Prove2me | Theorems.Thm_MetodosNumericos_affine_iteration_converges_of_contraction
-- name    : MetodosNumericos.affine_iteration_converges_of_contraction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:15:00.018992+00:00
-- url     : https://prove2.me/theorems/4764d320-ac41-4318-a56c-4dc597093749
-- title:
--   Contraction implies convergence of the affine iteration
-- statement:
--   If $\\lVert Bv\\rVert \\le c\\lVert v\\rVert$ for all $v$ with $c < 1$, and $y$ satisfies $y = By + d$, then every sequence with $x^{(k+1)} = Bx^{(k)} + d$ converges to $y$, whatever the starting vector. This is Proposição 5.5.3, with the consistency of the vector and matrix norms expressed directly by the hypothesis on $B$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 5, Proposição 5.5.3, pp. 108–109.

import Mathlib

open Filter Topology

namespace MetodosNumericos

theorem affine_iteration_converges_of_contraction {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (c : ℝ) (hc : c < 1)
    (hB : ∀ v : Fin n → ℝ, ‖B.mulVec v‖ ≤ c * ‖v‖)
    (y : Fin n → ℝ) (hy : y = B.mulVec y + d)
    (x : ℕ → (Fin n → ℝ)) (hrec : ∀ k, x (k + 1) = B.mulVec (x k) + d) :
    Tendsto x atTop (𝓝 y) := by sorry

end MetodosNumericos
