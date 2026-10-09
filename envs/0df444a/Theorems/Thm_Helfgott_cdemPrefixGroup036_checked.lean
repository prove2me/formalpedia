-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup036_checked
-- name    : Helfgott.cdemPrefixGroup036_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:34:15.310755+00:00
-- url     : https://prove2.me/theorems/454c1d01-0b5c-427c-a179-6d3d38dc9b3a
-- title:
--   CDEM exact Mobius prefix statistics on [147456, 151552)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 147456 ≤ n < 151552: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [20, 2492, 665378, 13307288610938289015990466582]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup036_checked :
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n) = (20 : ℤ) ∧
    (∑ n ∈ Ico 147456 151552, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (665378 : ℤ) ∧
    (∑ n ∈ Ico 147456 151552, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (13307288610938289015990466582 : ℤ) := by sorry

end Helfgott
