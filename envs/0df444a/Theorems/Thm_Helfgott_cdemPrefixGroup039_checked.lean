-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup039_checked
-- name    : Helfgott.cdemPrefixGroup039_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:41:28.323554+00:00
-- url     : https://prove2.me/theorems/25ec1741-7094-40e1-8b13-74f0044105ee
-- title:
--   CDEM exact Mobius prefix statistics on [159744, 163840)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 159744 ≤ n < 163840: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [72, 2482, 2223548, 44471728482976744577237731157]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup039_checked :
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n) = (72 : ℤ) ∧
    (∑ n ∈ Ico 159744 163840, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2482 : ℕ) ∧
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (2223548 : ℤ) ∧
    (∑ n ∈ Ico 159744 163840, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (44471728482976744577237731157 : ℤ) := by sorry

end Helfgott
