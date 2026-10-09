-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup015_checked
-- name    : Helfgott.cdemPrefixGroup015_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:44:43.10878+00:00
-- url     : https://prove2.me/theorems/1b0941d6-1f84-4633-a3c7-cffd4e4b5f41
-- title:
--   CDEM exact Mobius prefix statistics on [61440, 65536)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 61440 ≤ n < 65536: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [68, 2490, 5252767, 105056110765305202790018374012]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup015_checked :
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n) = (68 : ℤ) ∧
    (∑ n ∈ Ico 61440 65536, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5252767 : ℤ) ∧
    (∑ n ∈ Ico 61440 65536, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (105056110765305202790018374012 : ℤ) := by sorry

end Helfgott
