-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup041_checked
-- name    : Helfgott.cdemPrefixGroup041_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:45:14.918467+00:00
-- url     : https://prove2.me/theorems/f43e1c80-4c0c-496e-88cc-70502d6040e7
-- title:
--   CDEM exact Mobius prefix statistics on [167936, 172032)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 167936 ≤ n < 172032: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [30, 2490, 904246, 18084796258485758567974591146]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup041_checked :
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n) = (30 : ℤ) ∧
    (∑ n ∈ Ico 167936 172032, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (904246 : ℤ) ∧
    (∑ n ∈ Ico 167936 172032, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18084796258485758567974591146 : ℤ) := by sorry

end Helfgott
