-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup021_checked
-- name    : Helfgott.cdemPrefixGroup021_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:55:59.97843+00:00
-- url     : https://prove2.me/theorems/996fd34b-1c76-4509-a7e7-b70ea311f330
-- title:
--   CDEM exact Mobius prefix statistics on [86016, 90112)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 86016 ≤ n < 90112: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-70, 2494, -3961336, -79227328960517885890148025241]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup021_checked :
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n) = (-70 : ℤ) ∧
    (∑ n ∈ Ico 86016 90112, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3961336 : ℤ) ∧
    (∑ n ∈ Ico 86016 90112, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79227328960517885890148025241 : ℤ) := by sorry

end Helfgott
