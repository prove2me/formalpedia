-- Prove2me | Theorems.Thm_Gomory58_FractionalCut_cut_value_nonnegative
-- name    : Gomory58.FractionalCut.cut_value_nonnegative
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:46:55.541672+00:00
-- url     : https://prove2.me/theorems/56a3171a-d8cb-47ae-9aec-d22415362df1
-- title:
--   p. 277 — the new cut variable is nonnegative
-- statement:
--   For every nonnegative integer solution $(x',t')$ of tableau (2), the cut value $s_1$ satisfies
--
--   $$s_1\ge -f'_{i_0,0}>-1,\qquad s_1\ge0.$$
--
--   The first inequality follows from nonnegative fractional coefficients and nonnegative $t'_j$; together with integrality of $s_1$, it gives the second. This is the nonnegativity part of the extension to system (2*).
--
--   **Formalization Note** The Lean conclusion states the first and final inequalities; $-f'_{i_0,0}>-1$ is a property of the floor fractional part.
-- source:
--   Gomory, Outline of an algorithm for integer solutions to linear programs, Bull. Amer. Math. Soc. 64 (1958), https://doi.org/10.1090/S0002-9904-1958-10224-4, p. 277, paragraph 4 ("Furthermore, since …")

import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem cut_value_nonnegative {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ)
    (hsol : NonnegIntSol a x t) :
    -Int.fract (a i₀ 0) ≤ cutValue a i₀ t ∧ 0 ≤ cutValue a i₀ t := by sorry

end Gomory58.FractionalCut
