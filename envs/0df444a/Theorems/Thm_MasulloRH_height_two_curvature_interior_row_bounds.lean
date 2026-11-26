-- Prove2me | Theorems.Thm_MasulloRH_height_two_curvature_interior_row_bounds
-- name    : MasulloRH.height_two_curvature_interior_row_bounds
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T13:29:16.021801+00:00
-- url     : https://prove2.me/theorems/b0533253-e9c5-595e-be4f-d607f9549942
-- title:
--   Curvature budgets for the 816 central height-two cells
-- statement:
--   For each of the 816 indices $144\le j<960$, the existing height-two curvature table bounds the true cell energy by its group cap once the following elementary estimates are checked. Bound the two signed surrogate endpoint values by $A$, its absolute second derivative throughout the cell by $M\ge0$, and its explicit geometric tail throughout the cell by $E$. The right endpoint weight times $(A+M/131072+E)^2$ must fit the published cap in millionths. The constants can be chosen separately for each cell. The previously published directed dyadic and decimal computations cover these indices.
-- source:
--   The Masullo height-two theta-energy calculation https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e and its curvature-row theorem https://prove2.me/theorems/680e75e0-46e9-4f05-b70c-7f7de8530930.

import Definitions.Def_MasulloRH_HeightTwoCurvature
import Mathlib.Analysis.Calculus.Deriv.Basic

open MasulloRH.HeightTwoCurvature Set

theorem MasulloRH.height_two_curvature_interior_row_bounds (j : ℕ) (hL : 144 ≤ j) (hR : j < 960) :
    ∃ A M E : ℝ, 0 ≤ M ∧
      |surrogate j (edge j)| ≤ A ∧ |surrogate j (edge (j+1))| ≤ A ∧
      (∀ x ∈ Icc (edge j) (edge (j+1)),
        |deriv (deriv (surrogate j)) x| ≤ M ∧ tail j x ≤ E) ∧
      Real.exp (3/2 * edge (j+1) + 11/24 * |edge (j+1)|) *
        (A + M/131072 + E)^2 ≤ (cap j : ℝ)/1000000 := by sorry
