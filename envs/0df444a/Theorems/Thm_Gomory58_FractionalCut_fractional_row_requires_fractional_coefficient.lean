-- Prove2me | Theorems.Thm_Gomory58_FractionalCut_fractional_row_requires_fractional_coefficient
-- name    : Gomory58.FractionalCut.fractional_row_requires_fractional_coefficient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:46:47.793972+00:00
-- url     : https://prove2.me/theorems/ca759e89-8a61-459b-9001-fa3a4adeda42
-- title:
--   p. 277 — a fractional constant requires a fractional coefficient
-- statement:
--   Suppose the constant in the chosen tableau row has a nonzero fractional part and every other coefficient in that row has zero fractional part. Then the row equation cannot be satisfied with an integral row variable $x'_{i_0}$ and integral $t'_j$:
--
--   $$f'_{i_0,0}\ne0,\quad f'_{i_0,j}=0\ (1\le j\le n)
--   \quad\Longrightarrow\quad
--   \nexists (x',t')\text{ satisfying (2) with }x'_{i_0},t'_j\in\mathbb Z.$$
--
--   In particular, the tableau has no nonnegative integer solution. This makes precise the paper's observation that an integer solution needs some fractional coefficient in the selected row.
--
--   **Formalization Note** The paper omits primes on $f$ in this paragraph; the statement uses the primed tableau of (2).
-- source:
--   Gomory, Outline of an algorithm for integer solutions to linear programs, Bull. Amer. Math. Soc. 64 (1958), https://doi.org/10.1090/S0002-9904-1958-10224-4, p. 277, paragraph 2 ("It should be noted …")

import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem fractional_row_requires_fractional_coefficient {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1) → ℝ) (i₀ : Fin (m + 1))
    (hconst : Int.fract (a i₀ 0) ≠ 0)
    (hcoeff : ∀ j : Fin n, Int.fract (a i₀ j.succ) = 0) :
    ¬ ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
      TableauSol a x t ∧ IsInt (x i₀) ∧ (∀ j, IsInt (t j)) := by sorry

end Gomory58.FractionalCut
