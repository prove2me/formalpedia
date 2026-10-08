-- Prove2me | Theorems.Thm_Gomory58_FractionalCut_cut_value_integral
-- name    : Gomory58.FractionalCut.cut_value_integral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:46:52.80699+00:00
-- url     : https://prove2.me/theorems/672af8fc-8c9e-4fdd-b5d5-98e00f987a47
-- title:
--   p. 277 — the new cut variable is integral
-- statement:
--   For a solution $(x',t')$ of tableau (2), let $n'_{i_0,j}=\lfloor a'_{i_0,j}\rfloor$. When $x'_{i_0}$ and all $t'_j$ are integral, equation (3) has the identity
--
--   $$s_1=n'_{i_0,0}+\sum_{j=1}^n n'_{i_0,j}(-t'_j)-x'_{i_0}.$$
--
--   Consequently $s_1$ is integral. This supplies the integrality part of the extension from a solution of (2) to one of (2*). The identity is stated for tableau solutions with the integrality needed for its conclusion.
-- source:
--   Gomory, Outline of an algorithm for integer solutions to linear programs, Bull. Amer. Math. Soc. 64 (1958), https://doi.org/10.1090/S0002-9904-1958-10224-4, p. 277, paragraph 4 ("To see this suppose …")

import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem cut_value_integral {m n : ℕ} (a : Fin (m + 1) → Fin (n + 1) → ℝ)
    (i₀ : Fin (m + 1)) (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ)
    (hsol : TableauSol a x t) (hx : IsInt (x i₀)) (ht : ∀ j, IsInt (t j)) :
    cutValue a i₀ t =
      ((Int.floor (a i₀ 0) : ℝ) +
        (∑ j : Fin n, (Int.floor (a i₀ j.succ) : ℝ) * (-t j)) - x i₀) ∧
    IsInt (cutValue a i₀ t) := by sorry

end Gomory58.FractionalCut
