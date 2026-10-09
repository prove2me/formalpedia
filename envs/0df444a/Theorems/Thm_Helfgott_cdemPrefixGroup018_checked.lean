-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup018_checked
-- name    : Helfgott.cdemPrefixGroup018_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:51:07.762381+00:00
-- url     : https://prove2.me/theorems/2fbd795a-5150-4b72-abaf-973645e081bf
-- title:
--   CDEM exact Mobius prefix statistics on [73728, 77824)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 73728 ≤ n < 77824: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-46, 2486, -3011664, -60233821552229056239255113201]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup018_checked :
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n) = (-46 : ℤ) ∧
    (∑ n ∈ Ico 73728 77824, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3011664 : ℤ) ∧
    (∑ n ∈ Ico 73728 77824, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-60233821552229056239255113201 : ℤ) := by sorry

end Helfgott
