-- Prove2me | Theorems.Thm_MasulloRH_height_two_curvature_row_bounds
-- name    : MasulloRH.height_two_curvature_row_bounds
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T12:34:59.347086+00:00
-- url     : https://prove2.me/theorems/680e75e0-46e9-4f05-b70c-7f7de8530930
-- title:
--   Elementary endpoint, second derivative and truncation inequalities on 928 central height-two cells
-- statement:
--   For each index $80\le j<1008$, consider the real signed six-term surrogate on the cell of width $1/128$ starting at $-4+j/128$. There are constants $A,M,E$ controlling the two endpoint absolute values, the absolute second derivative everywhere in the cell and the explicit geometric tail everywhere in the cell. The right endpoint weight times $(A+M/131072+E)^2$ is at most the prescribed group cap in millionths. These are inequalities in explicit elementary functions. The remaining work is to certify them in Lean. Two independent directed-arithmetic computations checked all the proposed caps.
-- source:
--   Finite-height certificate for https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e with the rational witness https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d .

import Definitions.Def_MasulloRH_HeightTwoCurvature
import Mathlib.Analysis.Calculus.Deriv.Basic

open MasulloRH.HeightTwoCurvature Set

theorem MasulloRH.height_two_curvature_row_bounds (j : ℕ) (hL : 80 ≤ j) (hR : j < 1008) :
    ∃ A M E : ℝ, 0 ≤ M ∧
      |surrogate j (edge j)| ≤ A ∧ |surrogate j (edge (j+1))| ≤ A ∧
      (∀ x ∈ Icc (edge j) (edge (j+1)),
        |deriv (deriv (surrogate j)) x| ≤ M ∧ tail j x ≤ E) ∧
      Real.exp (3/2 * edge (j+1) + 11/24 * |edge (j+1)|) *
        (A + M/131072 + E)^2 ≤ (cap j : ℝ)/1000000 := by sorry
