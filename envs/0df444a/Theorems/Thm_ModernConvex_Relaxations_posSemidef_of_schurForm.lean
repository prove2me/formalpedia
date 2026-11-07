-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_posSemidef_of_schurForm
-- name    : ModernConvex.Relaxations.posSemidef_of_schurForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:30:17.183061+00:00
-- url     : https://prove2.me/theorems/996b974f-928a-4a3a-95a5-73d29a0a175a
-- title:
--   Nonnegative Schur form at a positive pivot implies positive semidefiniteness
-- statement:
--   **Nonnegative Schur form at a positive pivot implies $M\succeq0$.**
--
--   Let $M$ be real symmetric and let $M_{ii}>0$. If the Schur form $Q_i$ is nonnegative for every $v$, then $M$ is positive semidefinite.
--
--   Indeed, by completing the square, $v^{\mathsf T}Mv=M_{ii}(v_i+M_{ii}^{-1}P)^2+Q_i(v)$, and both terms are nonnegative: the first because $M_{ii}>0$ and a square is nonnegative, the second by hypothesis. Together with symmetry this is precisely positive semidefiniteness, by the quadratic-form characterisation.
--
--   This is the "accept" arm of the elimination step: having recursed successfully on the smaller form, one concludes the original matrix is semidefinite.
-- source:
--   Completing the square at a positive pivot; accept arm of the symmetric-elimination PSD test.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_SchurForm

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **PSD from a nonnegative Schur form.** -/
theorem posSemidef_of_schurForm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : 0 < M i i) (h : ∀ w : Fin n → ℝ, 0 ≤ schurForm M i w) :
    M.PosSemidef := by sorry

end ModernConvex.Relaxations
