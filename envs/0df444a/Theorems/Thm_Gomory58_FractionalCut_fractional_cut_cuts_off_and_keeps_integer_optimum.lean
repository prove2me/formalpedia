-- Prove2me | Theorems.Thm_Gomory58_FractionalCut_fractional_cut_cuts_off_and_keeps_integer_optimum
-- name    : Gomory58.FractionalCut.fractional_cut_cuts_off_and_keeps_integer_optimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:47:03.102517+00:00
-- url     : https://prove2.me/theorems/c779020e-1458-4449-9cc1-d7e36ede3693
-- title:
--   p. 277 — the fractional cut preserves the integer optimum
-- statement:
--   For the real tableau (2), choose a row $i_0$ whose constant $a'_{i_0,0}$ is nonintegral, and adjoin the fractional cut (3) to form (2*). The simplex point $(x'_i,t'_j)=(a'_{i,0},0)$ solves (2), but its associated $s_1$ is negative and so is infeasible for (2*). Every nonnegative integer solution $(x',t')$ of (2) extends uniquely by its cut value to a nonnegative integer solution $(x',t',s_1)$ of (2*), and every such solution of (2*) projects back by dropping $s_1$. The objective $w=x'_0$ is unchanged. Consequently, for every real $W$,
--
--   $$W\text{ is a greatest attained integer-feasible }w\text{-value for (2)}
--   \iff W\text{ is one for (2*).}$$
--
--   The equivalence covers empty and unbounded objective-value sets without assigning them an artificial maximum. It formalizes the paper's assertion that integer maximization may proceed in the augmented system.
--
--   **Formalization Note** The selected row may be row $0$ because the argument only needs that row's variable to be integral; the paper selects a constraint row. The statement does not assume nonnegative tableau constants or objective coefficients, which the cut correspondence does not require.
-- source:
--   Gomory, Outline of an algorithm for integer solutions to linear programs, Bull. Amer. Math. Soc. 64 (1958), https://doi.org/10.1090/S0002-9904-1958-10224-4, p. 277, paragraphs 3–5 ("Since the simplex solution …" through "dropping the s₁")

import Mathlib
import Definitions.Def_Gomory58_FractionalCut_Tableau

namespace Gomory58.FractionalCut

theorem fractional_cut_cuts_off_and_keeps_integer_optimum {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1) → ℝ) (i₀ : Fin (m + 1))
    (h : ¬ IsInt (a i₀ 0)) :
    TableauSol a (fun i => a i 0) (fun _ => 0) ∧
    cutValue a i₀ (fun _ => 0) = -Int.fract (a i₀ 0) ∧
    ¬ FeasibleStar a i₀ (fun i => a i 0) (fun _ => 0)
      (cutValue a i₀ (fun _ => 0)) ∧
    (∀ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
      NonnegIntSol a x t ↔ NonnegIntSolStar a i₀ x t (cutValue a i₀ t)) ∧
    (∀ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ),
      NonnegIntSolStar a i₀ x t s → s = cutValue a i₀ t) ∧
    (∀ W : ℝ,
      IsGreatest {v : ℝ | ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ),
        NonnegIntSol a x t ∧ x 0 = v} W ↔
      IsGreatest {v : ℝ | ∃ (x : Fin (m + 1) → ℝ) (t : Fin n → ℝ) (s : ℝ),
        NonnegIntSolStar a i₀ x t s ∧ x 0 = v} W) := by sorry

end Gomory58.FractionalCut
