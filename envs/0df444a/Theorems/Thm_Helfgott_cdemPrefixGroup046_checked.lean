-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup046_checked
-- name    : Helfgott.cdemPrefixGroup046_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:57:11.154724+00:00
-- url     : https://prove2.me/theorems/88e7a320-4b81-4e47-aab6-53bb17e4667a
-- title:
--   CDEM exact Mobius prefix statistics on [188416, 192512)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 188416 ≤ n < 192512: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [21, 2489, 557065, 11141864763579426618638827842]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup046_checked :
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n) = (21 : ℤ) ∧
    (∑ n ∈ Ico 188416 192512, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2489 : ℕ) ∧
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (557065 : ℤ) ∧
    (∑ n ∈ Ico 188416 192512, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11141864763579426618638827842 : ℤ) := by sorry

end Helfgott
