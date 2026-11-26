-- Prove2me | Theorems.Thm_MasulloRH_height_two_curvature_tail_rows
-- name    : MasulloRH.height_two_curvature_tail_rows
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T13:29:12.284332+00:00
-- url     : https://prove2.me/theorems/af2f2710-3a61-4d49-bd22-d4d982750db2
-- title:
--   Curvature budgets and true residual density for 208 outer height-two cells
-- statement:
--   On the height-two mesh of width $1/128$, let $0\le j<144$ or $960\le j<1024$. Every such cell satisfies the published curvature budget for the fixed eleven-term witness, including both endpoint bounds, a bound for the second derivative everywhere, and a bound for the truncation error. In addition, the true weighted squared residual of the infinite theta function is at most $10^{-8}$ everywhere in the cell.
-- source:
--   The Masullo height-two theta-energy calculation https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e and its curvature-row theorem https://prove2.me/theorems/680e75e0-46e9-4f05-b70c-7f7de8530930.

import Definitions.Def_MasulloRH_HeightTwoCurvature
import Definitions.Def_MasulloRH_GaussianThetaApproximation

open MasulloRH MasulloRH.HeightTwoCurvature MasulloRH.GaussianApproximation Set

theorem MasulloRH.height_two_curvature_tail_rows (j : ℕ) (hj : j < 1024) (hs : j < 144 ∨ 960 ≤ j) :
    (∃ A M E : ℝ, 0 ≤ M ∧
      |surrogate j (edge j)| ≤ A ∧ |surrogate j (edge (j+1))| ≤ A ∧
      (∀ x ∈ Icc (edge j) (edge (j+1)),
        |deriv (deriv (surrogate j)) x| ≤ M ∧ tail j x ≤ E) ∧
      Real.exp (3/2 * edge (j+1) + 11/24 * |edge (j+1)|) *
        (A + M/131072 + E)^2 ≤ (cap j : ℝ)/1000000) ∧
      ∀ x ∈ Icc (edge j) (edge (j+1)), Real.exp (2*(3/4)*x + 2*(11/48)*|x|) *
        ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2 ≤ 1/100000000 := by sorry
