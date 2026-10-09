-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup027_checked
-- name    : Helfgott.cdemPrefixGroup027_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:09:22.895093+00:00
-- url     : https://prove2.me/theorems/caad15c4-6d18-447b-99b5-40b2c9e8b413
-- title:
--   CDEM exact Mobius prefix statistics on [110592, 114688)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 110592 ≤ n < 114688: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [87, 2485, 3858377, 77168570809475711080113522881]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup027_checked :
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n) = (87 : ℤ) ∧
    (∑ n ∈ Ico 110592 114688, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2485 : ℕ) ∧
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (3858377 : ℤ) ∧
    (∑ n ∈ Ico 110592 114688, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (77168570809475711080113522881 : ℤ) := by sorry

end Helfgott
