-- Prove2me | Theorems.Thm_MetodosNumericos_jacobi_fixed_point_equiv
-- name    : MetodosNumericos.jacobi_fixed_point_equiv
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:32:32.635245+00:00
-- url     : https://prove2.me/theorems/7a57d90b-b965-4474-bee3-ffd2a045221e
-- title:
--   The fixed points of the Jacobi sweep are the solutions of $Ax=b$
-- statement:
--   If all diagonal entries of $A$ are nonzero, then a vector $x$ satisfies $Ax = b$ if and only if it is unchanged by the Jacobi sweep. This is the equivalence $Ax = b \\iff x = Bx + d$ of Proposição 5.5.2, stated for the Jacobi splitting.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 5, Proposição 5.5.2, pp. 107–108.

import Mathlib
import Definitions.Def_MetodosNumericos_sistemasDefs

namespace MetodosNumericos

theorem jacobi_fixed_point_equiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (hdiag : ∀ i, A i i ≠ 0) (x : Fin n → ℝ) :
    A.mulVec x = b ↔ jacobiSweep A b x = x := by sorry

end MetodosNumericos
