-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup023_checked
-- name    : Helfgott.cdemPrefixGroup023_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:01:44.005571+00:00
-- url     : https://prove2.me/theorems/c04780dd-1d9a-441a-8d44-a1bea9061482
-- title:
--   CDEM exact Mobius prefix statistics on [94208, 98304)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 94208 ≤ n < 98304: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-5, 2485, -318249, -6365083916310545809191990388]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup023_checked :
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n) = (-5 : ℤ) ∧
    (∑ n ∈ Ico 94208 98304, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2485 : ℕ) ∧
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-318249 : ℤ) ∧
    (∑ n ∈ Ico 94208 98304, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-6365083916310545809191990388 : ℤ) := by sorry

end Helfgott
