-- Prove2me | Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_respects_fixed_priority
-- name    : NisanRonen.Rounding.boundedLoadDP_respects_fixed_priority
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:42.786036+00:00
-- url     : https://prove2.me/theorems/f0d7132a-75e8-51b7-a153-56a1ef312803
-- title:
--   Bounded load-vector dynamic programming chooses the first optimum in a fixed order
-- statement:
--   For a fixed number of machines and tasks, there is a report-independent injective natural-number rank on allocations. At every in-box profile the bounded load-vector dynamic program returns the minimum-ranked allocation among those with the same rounded makespan as the output. This rank can be taken to be the base-machine-count code of the assignment list, with the first task as the least significant digit.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9, https://doi.org/10.1006/game.1999.0790. Tie-breaking of the formalized exact rounded solver.

import Definitions.Def_NisanRonen_Rounding_boundedLoadDP
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

namespace NisanRonen.Rounding

theorem boundedLoadDP_respects_fixed_priority {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (n : ℕ) [NeZero n] (k : ℕ) :
    ∃ rank : (Fin k → Fin n) → ℕ, Function.Injective rank ∧
      ∀ d : Fin n → Fin k → ℝ, (∀ l j, a ≤ d l j ∧ d l j ≤ b) →
        let f := boundedLoadDP (n := n) (⌈b / δ⌉.toNat)
        let x := allocOf f δ d
        ∀ y : Fin k → Fin n, roundedMakespan δ y (corrStar y d) =
          roundedMakespan δ x (corrStar x d) → rank x ≤ rank y := by sorry

end NisanRonen.Rounding
