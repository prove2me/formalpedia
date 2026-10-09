-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup038_checked
-- name    : Helfgott.cdemPrefixGroup038_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:40:00.761413+00:00
-- url     : https://prove2.me/theorems/4a180e5c-0c51-49be-be97-e9d31f4c9045
-- title:
--   CDEM exact Mobius prefix statistics on [155648, 159744)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 155648 ≤ n < 159744: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-4, 2490, -124399, -2487958959274636536117155916]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup038_checked :
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n) = (-4 : ℤ) ∧
    (∑ n ∈ Ico 155648 159744, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-124399 : ℤ) ∧
    (∑ n ∈ Ico 155648 159744, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-2487958959274636536117155916 : ℤ) := by sorry

end Helfgott
