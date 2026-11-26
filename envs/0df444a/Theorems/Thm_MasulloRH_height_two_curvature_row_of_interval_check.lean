-- Prove2me | Theorems.Thm_MasulloRH_height_two_curvature_row_of_interval_check
-- name    : MasulloRH.height_two_curvature_row_of_interval_check
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T14:05:57.332804+00:00
-- url     : https://prove2.me/theorems/b1f15950-5e6c-4a63-8ee3-6f4bf54d7845
-- title:
--   A successful rational check certifies a full real height-two curvature row
-- statement:
--   For any natural index $j$ for which the rational interval check returns true, the published Masullo curvature budget holds. It bounds the signed surrogate at both endpoints, its absolute second derivative at every real point of the closed cell, and the truncation tail there, with constants satisfying the required weighted inequality.
-- source:
--   The Masullo height-two certificate https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e and its central curvature-row theorem https://prove2.me/theorems/b0533253-e9c5-595e-be4f-d607f9549942.

import Definitions.Def_MasulloRH_InteriorEvaluator
import Mathlib.Analysis.Calculus.Deriv.Basic

open MasulloRH.InteriorEvaluator MasulloRH.HeightTwoCurvature Set

theorem MasulloRH.height_two_curvature_row_of_interval_check (j : ℕ) (h : passes j = true) :
    ∃ A M E : ℝ, 0 ≤ M ∧
      |surrogate j (edge j)| ≤ A ∧ |surrogate j (edge (j+1))| ≤ A ∧
      (∀ x ∈ Icc (edge j) (edge (j+1)),
        |deriv (deriv (surrogate j)) x| ≤ M ∧ tail j x ≤ E) ∧
      Real.exp (3/2 * edge (j+1) + 11/24 * |edge (j+1)|) *
        (A + M/131072 + E)^2 ≤ (cap j : ℝ)/1000000 := by sorry
