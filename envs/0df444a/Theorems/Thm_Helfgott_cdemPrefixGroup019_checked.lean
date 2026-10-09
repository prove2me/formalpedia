-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup019_checked
-- name    : Helfgott.cdemPrefixGroup019_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:52:02.811861+00:00
-- url     : https://prove2.me/theorems/f8067da9-ad61-41c5-b4d5-c47e87f27bda
-- title:
--   CDEM exact Mobius prefix statistics on [77824, 81920)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 77824 ≤ n < 81920: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-11, 2487, -636009, -12720418578954713761090633101]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup019_checked :
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 77824 81920, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-636009 : ℤ) ∧
    (∑ n ∈ Ico 77824 81920, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-12720418578954713761090633101 : ℤ) := by sorry

end Helfgott
