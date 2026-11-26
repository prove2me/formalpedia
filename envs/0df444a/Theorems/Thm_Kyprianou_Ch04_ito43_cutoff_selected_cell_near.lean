-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_selected_cell_near
-- name    : Kyprianou.Ch04.ito43_cutoff_selected_cell_near
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:48:33.620268+00:00
-- url     : https://prove2.me/theorems/51a30d7c-28fa-4887-be3b-ec09ed98f90f
-- title:
--   Every point of a selected shrinking cell is close to its atom
-- statement:
--   The selected interval contains the atom and has width T divided by n. Bound each point distance by this vanishing width.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_selected_cell_near (T s : NNReal) (j : ℕ → ℕ)
    (hj : ∀ᶠ n : ℕ in atTop,
      j n < n ∧ T * (j n : NNReal) / (n : NNReal) < s ∧
      s ≤ T * ((j n+1 : ℕ) : NNReal) / (n : NNReal)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      let a := T * (j n : NNReal) / (n : NNReal)
      let b := T * ((j n+1 : ℕ) : NNReal) / (n : NNReal)
      a < s ∧ s ≤ b ∧ ∀ r ∈ Icc a b, dist r s < δ := by sorry
