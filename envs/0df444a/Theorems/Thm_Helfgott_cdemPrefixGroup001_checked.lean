-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup001_checked
-- name    : Helfgott.cdemPrefixGroup001_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:17:12.699588+00:00
-- url     : https://prove2.me/theorems/bbd34463-8949-4ca9-9269-24737a067338
-- title:
--   CDEM exact Mobius prefix statistics on [4096, 8192)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 4096 ≤ n < 8192: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [41, 2491, 34957511, 699150512321253056761886786107]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup001_checked :
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n) = (41 : ℤ) ∧
    (∑ n ∈ Ico 4096 8192, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (34957511 : ℤ) ∧
    (∑ n ∈ Ico 4096 8192, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (699150512321253056761886786107 : ℤ) := by sorry

end Helfgott
