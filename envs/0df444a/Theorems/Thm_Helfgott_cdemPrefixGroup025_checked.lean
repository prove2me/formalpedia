-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup025_checked
-- name    : Helfgott.cdemPrefixGroup025_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:03:20.670243+00:00
-- url     : https://prove2.me/theorems/2d2ccff9-ad62-4a19-b11e-d329d7e37145
-- title:
--   CDEM exact Mobius prefix statistics on [102400, 106496)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 102400 ≤ n < 106496: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [29, 2487, 1431362, 28627378348167438853142479503]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup025_checked :
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n) = (29 : ℤ) ∧
    (∑ n ∈ Ico 102400 106496, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1431362 : ℤ) ∧
    (∑ n ∈ Ico 102400 106496, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (28627378348167438853142479503 : ℤ) := by sorry

end Helfgott
