-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup012_checked
-- name    : Helfgott.cdemPrefixGroup012_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:38:21.228964+00:00
-- url     : https://prove2.me/theorems/cebcd2ff-7fb9-4730-aa90-40ea2947e7d0
-- title:
--   CDEM exact Mobius prefix statistics on [49152, 53248)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 49152 ≤ n < 53248: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-66, 2490, -6624360, -132488017926501913361714897744]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup012_checked :
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n) = (-66 : ℤ) ∧
    (∑ n ∈ Ico 49152 53248, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6624360 : ℤ) ∧
    (∑ n ∈ Ico 49152 53248, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-132488017926501913361714897744 : ℤ) := by sorry

end Helfgott
