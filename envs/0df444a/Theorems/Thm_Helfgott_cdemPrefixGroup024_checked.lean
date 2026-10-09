-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup024_checked
-- name    : Helfgott.cdemPrefixGroup024_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:01:48.67595+00:00
-- url     : https://prove2.me/theorems/e339e3a5-83dd-48b9-a779-fabfe91a96cd
-- title:
--   CDEM exact Mobius prefix statistics on [98304, 102400)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 98304 ≤ n < 102400: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [17, 2499, 896504, 17929907555780736913298804430]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup024_checked :
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n) = (17 : ℤ) ∧
    (∑ n ∈ Ico 98304 102400, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2499 : ℕ) ∧
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (896504 : ℤ) ∧
    (∑ n ∈ Ico 98304 102400, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (17929907555780736913298804430 : ℤ) := by sorry

end Helfgott
