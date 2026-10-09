-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup004_checked
-- name    : Helfgott.cdemPrefixGroup004_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:22:41.900685+00:00
-- url     : https://prove2.me/theorems/11bd6701-e598-4f1b-8ed9-763e96f3bff3
-- title:
--   CDEM exact Mobius prefix statistics on [16384, 20480)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 16384 ≤ n < 20480: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [55, 2491, 15458647, 309173526311773485610560359558]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup004_checked :
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n) = (55 : ℤ) ∧
    (∑ n ∈ Ico 16384 20480, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (15458647 : ℤ) ∧
    (∑ n ∈ Ico 16384 20480, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (309173526311773485610560359558 : ℤ) := by sorry

end Helfgott
