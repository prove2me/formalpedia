-- Prove2me | Theorems.Thm_Gomory58_FractionalCut_drop_slack
-- name    : Gomory58.FractionalCut.drop_slack
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:46:35.918208+00:00
-- url     : https://prove2.me/theorems/8a822ea3-4b64-4dc6-9b9b-2d4cbce0ec93
-- title:
--   p. 277 — dropping the slack variable
-- statement:
--   Every feasible solution of the augmented system (2*) projects to a feasible solution of the original tableau (2) by dropping $s_1$. The same projection sends each nonnegative integer solution of (2*) to a nonnegative integer solution of (2):
--
--   $$ (x',t',s_1)\in\mathcal F_{2^*}\Longrightarrow (x',t')\in\mathcal F_2. $$
--
--   Here the integer version uses the corresponding nonnegative integer feasible sets. This projection is one direction of the solution correspondence.
-- source:
--   Gomory, Outline of an algorithm for integer solutions to linear programs, Bull. Amer. Math. Soc. 64 (1958), https://doi.org/10.1090/S0002-9904-1958-10224-4, p. 277, paragraph 1 ("Clearly any feasible solution …")

import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem drop_slack {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ) :
    (FeasibleStar a i₀ x t s → FeasibleSol a x t) ∧
    (NonnegIntSolStar a i₀ x t s → NonnegIntSol a x t) := by sorry

end Gomory58.FractionalCut
