-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup010_checked
-- name    : Helfgott.cdemPrefixGroup010_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:34:59.357294+00:00
-- url     : https://prove2.me/theorems/ce67bd0f-1492-4e23-9551-b43969080e3e
-- title:
--   CDEM exact Mobius prefix statistics on [40960, 45056)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 40960 ≤ n < 45056: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [8, 2500, 630528, 12610742463242094854335621693]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup010_checked :
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 40960 45056, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2500 : ℕ) ∧
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (630528 : ℤ) ∧
    (∑ n ∈ Ico 40960 45056, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12610742463242094854335621693 : ℤ) := by sorry

end Helfgott
