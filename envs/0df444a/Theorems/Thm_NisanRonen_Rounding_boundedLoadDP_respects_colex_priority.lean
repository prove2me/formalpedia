-- Prove2me | Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_respects_colex_priority
-- name    : NisanRonen.Rounding.boundedLoadDP_respects_colex_priority
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:07:03.582639+00:00
-- url     : https://prove2.me/theorems/fb673f19-03f6-4b1a-a87f-2c25aa8970ba
-- title:
--   The bounded scheduling dynamic program picks the first optimal assignment in colexicographic order
-- statement:
--   For each bounded rounded scheduling instance, among the allocations tied with the dynamic program’s output, the output minimizes the base-n rank whose first job is the least significant digit.
-- source:
--   Explicit form of the fixed-priority property of the bounded load dynamic program in Algorithmic Mechanism Design VIII.

import Definitions.Def_NisanRonen_Rounding_boundedLoadDP
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

namespace NisanRonen.Rounding

theorem boundedLoadDP_respects_colex_priority {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (n : ℕ) [NeZero n] (k : ℕ) :
    ∀ d : Fin n → Fin k → ℝ, (∀ l j, a ≤ d l j ∧ d l j ≤ b) →
        let f := boundedLoadDP (n := n) (⌈b / δ⌉.toNat)
        let x := allocOf f δ d
        ∀ y : Fin k → Fin n, roundedMakespan δ y (corrStar y d) =
          roundedMakespan δ x (corrStar x d) →
          (List.ofFn x).foldr (fun i r => i.val + n * r) 0 ≤
            (List.ofFn y).foldr (fun i r => i.val + n * r) 0 := by sorry

end NisanRonen.Rounding
