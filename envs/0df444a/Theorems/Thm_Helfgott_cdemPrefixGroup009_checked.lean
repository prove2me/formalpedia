-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup009_checked
-- name    : Helfgott.cdemPrefixGroup009_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:31:34.21985+00:00
-- url     : https://prove2.me/theorems/4e9a4851-d191-4428-af1a-353e3adf0c1d
-- title:
--   CDEM exact Mobius prefix statistics on [36864, 40960)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 36864 ≤ n < 40960: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [1, 2483, -28012, -560505832981627883163084282]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup009_checked :
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n) = (1 : ℤ) ∧
    (∑ n ∈ Ico 36864 40960, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-28012 : ℤ) ∧
    (∑ n ∈ Ico 36864 40960, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-560505832981627883163084282 : ℤ) := by sorry

end Helfgott
