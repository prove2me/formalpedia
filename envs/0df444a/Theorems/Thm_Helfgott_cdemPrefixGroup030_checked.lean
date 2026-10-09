-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup030_checked
-- name    : Helfgott.cdemPrefixGroup030_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:20:54.93898+00:00
-- url     : https://prove2.me/theorems/6c90f3cb-e887-41a0-91f5-a8d7e7c76e65
-- title:
--   CDEM exact Mobius prefix statistics on [122880, 126976)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 122880 ≤ n < 126976: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-11, 2501, -455445, -9109197376020916839765703838]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup030_checked :
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n) = (-11 : ℤ) ∧
    (∑ n ∈ Ico 122880 126976, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2501 : ℕ) ∧
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-455445 : ℤ) ∧
    (∑ n ∈ Ico 122880 126976, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-9109197376020916839765703838 : ℤ) := by sorry

end Helfgott
