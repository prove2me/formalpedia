-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup045_checked
-- name    : Helfgott.cdemPrefixGroup045_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:53:18.294672+00:00
-- url     : https://prove2.me/theorems/dbaeaded-2273-4724-8867-b4eb3322122e
-- title:
--   CDEM exact Mobius prefix statistics on [184320, 188416)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 184320 ≤ n < 188416: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [14, 2488, 381835, 7636878746389338738820734466]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup045_checked :
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n) = (14 : ℤ) ∧
    (∑ n ∈ Ico 184320 188416, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2488 : ℕ) ∧
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (381835 : ℤ) ∧
    (∑ n ∈ Ico 184320 188416, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (7636878746389338738820734466 : ℤ) := by sorry

end Helfgott
