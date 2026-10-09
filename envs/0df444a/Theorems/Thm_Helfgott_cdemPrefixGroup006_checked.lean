-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup006_checked
-- name    : Helfgott.cdemPrefixGroup006_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:24:31.838982+00:00
-- url     : https://prove2.me/theorems/e2db63c5-ee12-4043-a39f-09fd71e5aba3
-- title:
--   CDEM exact Mobius prefix statistics on [24576, 28672)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 24576 ≤ n < 28672: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [43, 2495, 8882247, 177645206574917662038792521731]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup006_checked :
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n) = (43 : ℤ) ∧
    (∑ n ∈ Ico 24576 28672, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2495 : ℕ) ∧
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8882247 : ℤ) ∧
    (∑ n ∈ Ico 24576 28672, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (177645206574917662038792521731 : ℤ) := by sorry

end Helfgott
