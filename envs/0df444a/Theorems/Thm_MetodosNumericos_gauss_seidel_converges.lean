-- Prove2me | Theorems.Thm_MetodosNumericos_gauss_seidel_converges
-- name    : MetodosNumericos.gauss_seidel_converges
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:34:28.759316+00:00
-- url     : https://prove2.me/theorems/80cc9787-4519-42e8-ab92-aa8a4f43291f
-- title:
--   Gauss-Seidel converges for diagonally dominant matrices
-- statement:
--   Let $A$ be diagonally dominant, $|a_{ii}| > \\sum_{j\\neq i}|a_{ij}|$ for every row $i$, and let $x^\\star$ satisfy $Ax^\\star = b$. Then, from any starting vector, the Gauss-Seidel iterates converge to $x^\\star$. This is Proposição 5.10.1; the source states it for the start $x^{(0)} = 0$, and the formal statement allows an arbitrary start.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 5, Proposição 5.10.1, pp. 113–116.

import Mathlib
import Definitions.Def_MetodosNumericos_sistemasDefs

open Filter Topology

namespace MetodosNumericos

theorem gauss_seidel_converges {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b xstar x0 : Fin n → ℝ)
    (hA : DiagDominant A) (hsol : A.mulVec xstar = b) :
    Tendsto (gaussSeidelSeq A b x0) atTop (𝓝 xstar) := by sorry

end MetodosNumericos
