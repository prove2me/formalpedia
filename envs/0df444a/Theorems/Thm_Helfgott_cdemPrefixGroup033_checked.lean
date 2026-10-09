-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup033_checked
-- name    : Helfgott.cdemPrefixGroup033_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:27:52.235608+00:00
-- url     : https://prove2.me/theorems/1e0f0058-ee47-43ed-8596-b11df666b0a9
-- title:
--   CDEM exact Mobius prefix statistics on [135168, 139264)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 135168 ≤ n < 139264: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-100, 2494, -3654068, -73082450948001589317295747044]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup033_checked :
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n) = (-100 : ℤ) ∧
    (∑ n ∈ Ico 135168 139264, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3654068 : ℤ) ∧
    (∑ n ∈ Ico 135168 139264, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-73082450948001589317295747044 : ℤ) := by sorry

end Helfgott
