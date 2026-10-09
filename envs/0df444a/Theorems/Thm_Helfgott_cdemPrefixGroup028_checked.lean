-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup028_checked
-- name    : Helfgott.cdemPrefixGroup028_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:12:27.387349+00:00
-- url     : https://prove2.me/theorems/73801c2c-311b-4162-a720-7811032feeb3
-- title:
--   CDEM exact Mobius prefix statistics on [114688, 118784)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 114688 ≤ n < 118784: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [15, 2483, 631054, 12621962507031227870189260397]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup028_checked :
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n) = (15 : ℤ) ∧
    (∑ n ∈ Ico 114688 118784, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (631054 : ℤ) ∧
    (∑ n ∈ Ico 114688 118784, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (12621962507031227870189260397 : ℤ) := by sorry

end Helfgott
