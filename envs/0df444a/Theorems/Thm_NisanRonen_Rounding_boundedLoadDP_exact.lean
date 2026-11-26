-- Prove2me | Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_exact
-- name    : NisanRonen.Rounding.boundedLoadDP_exact
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:35:07.534345+00:00
-- url     : https://prove2.me/theorems/6b22df80-64b7-5edb-9150-7acee6b604fa
-- title:
--   The load-vector dynamic program exactly solves the rounded instance
-- statement:
--   Let there be at least one machine, let the grid spacing be positive, and let the declarations be bounded below by a positive number and above by $b$. Round each declaration up to an integer number of grid units. The load-vector dynamic program with cap equal to the ceiling of $b$ divided by the grid spacing returns one machine for each task. Its allocation minimizes the makespan at the rounded declarations over all allocations.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, p. 192, https://doi.org/10.1006/game.1999.0790. The exact dynamic-programming step on the rounded instance.

import Definitions.Def_NisanRonen_Rounding_boundedLoadDP
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

namespace NisanRonen.Rounding

theorem boundedLoadDP_exact {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (n : ℕ) [NeZero n] :
    IsExactRoundedSolver (boundedLoadDP (n := n) (⌈b / δ⌉.toNat)) δ a b := by sorry

end NisanRonen.Rounding
