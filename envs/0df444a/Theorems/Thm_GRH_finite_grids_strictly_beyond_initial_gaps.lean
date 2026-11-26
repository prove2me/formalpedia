-- Prove2me | Theorems.Thm_GRH_finite_grids_strictly_beyond_initial_gaps
-- name    : GRH.finite_grids_strictly_beyond_initial_gaps
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T16:15:54.468799+00:00
-- url     : https://prove2.me/theorems/1bb90a81-2dea-4e38-80a2-05633dc3868b
-- title:
--   Passing Dirichlet grids beyond the initial-gap test at prime seven and at height three
-- statement:
--   At the first target grid, consider the divisors of $42$ which are multiples of $7$. At the third target grid, consider divisors of $6$. In each case the initial-gap test provably fails and the Dirichlet-polynomial grid nevertheless passes for every nonprincipal character. These are instances of the former open primitive-grid assertion whenever the character is primitive.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletGrid
import Definitions.Def_GRH_DirichletPeriod

theorem GRH.finite_grids_strictly_beyond_initial_gaps (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (h : ℕ) (hc : (h=0 ∧ d ∣ 42 ∧ 7 ∣ d) ∨ (h=2 ∧ d ∣ 6)) :
    (¬ GRH.DirichletPeriod.Covers d (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1)) ∧
    ∃ m : ℕ, GRH.DirichletGrid.Passes χ
      (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by sorry
