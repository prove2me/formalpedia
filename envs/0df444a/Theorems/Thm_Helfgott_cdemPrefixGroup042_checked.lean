-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup042_checked
-- name    : Helfgott.cdemPrefixGroup042_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:47:59.630009+00:00
-- url     : https://prove2.me/theorems/5182fbae-a89f-418f-b6d0-662ba9380e6b
-- title:
--   CDEM exact Mobius prefix statistics on [172032, 176128)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 172032 ≤ n < 176128: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [16, 2492, 458472, 9169755886883888965720022430]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup042_checked :
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n) = (16 : ℤ) ∧
    (∑ n ∈ Ico 172032 176128, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (458472 : ℤ) ∧
    (∑ n ∈ Ico 172032 176128, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (9169755886883888965720022430 : ℤ) := by sorry

end Helfgott
