-- Prove2me | Theorems.Thm_Gomory58_FractionalCut_cut_off_simplex
-- name    : Gomory58.FractionalCut.cut_off_simplex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:46:49.912984+00:00
-- url     : https://prove2.me/theorems/fe45c793-2f50-40d4-a4ee-b4a6bc710140
-- title:
--   p. 277 — the cut excludes the simplex solution
-- statement:
--   At the simplex point $t'=0$, the cut variable equals the negative fractional part of the selected row's constant. If that constant is not an integer, then
--
--   $$s_1(0)=-f'_{i_0,0}<0.$$
--
--   Thus the corresponding augmented point cannot satisfy the nonnegativity requirement on $s_1$. This is the cut-off property of equation (3).
-- source:
--   Gomory, Outline of an algorithm for integer solutions to linear programs, Bull. Amer. Math. Soc. 64 (1958), https://doi.org/10.1090/S0002-9904-1958-10224-4, p. 277, paragraph 3 ("Since the simplex solution …")

import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem cut_off_simplex {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (h : ¬ IsInt (a i₀ 0)) :
    cutValue a i₀ (fun _ => 0) = -Int.fract (a i₀ 0) ∧
    cutValue a i₀ (fun _ => 0) < 0 := by sorry

end Gomory58.FractionalCut
