-- Prove2me | Theorems.Thm_Kyprianou_Ch02_equalGridRefinementExistsV1
-- name    : Kyprianou.Ch02.equalGridRefinementExistsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:42:16.304116+00:00
-- url     : https://prove2.me/theorems/abdefd9d-005e-44b8-843f-db0e86222ceb
-- title:
--   A monotone partition has a concatenated equal-cell refinement
-- statement:
--   Concatenate the subdivisions in chronological order. Use the quotient and remainder of the fine-grid index by n+1 to identify its block and cell, with the last endpoint t(last). At block boundaries the endpoint formula agrees with the next block start. Monotonicity follows within a block and across successive blocks.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.equalGridRefinementExistsV1
    (n m : ℕ) (t : Fin (m+1) → ℝ≥0) (ht : Monotone t) :
    ∃ v : Fin (m*(n+1)+1) → ℝ≥0, Monotone v ∧
      ∀ (i : Fin m) (j : Fin (n+1)),
        let k := finProdFinEquiv (i,j)
        let a := t i.castSucc
        let b := t i.succ
        v k.castSucc = a+(b-a)*(j.val : ℝ≥0)/((n+1 : ℕ) : ℝ≥0) ∧
        v k.succ = a+(b-a)*((j.val+1 : ℕ) : ℝ≥0)/((n+1 : ℕ) : ℝ≥0) := by sorry
