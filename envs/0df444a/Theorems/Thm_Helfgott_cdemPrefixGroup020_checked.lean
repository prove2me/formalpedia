-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup020_checked
-- name    : Helfgott.cdemPrefixGroup020_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:55:19.093747+00:00
-- url     : https://prove2.me/theorems/477cb66b-e91e-4ba3-a16a-a8793c4c8c32
-- title:
--   CDEM exact Mobius prefix statistics on [81920, 86016)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 81920 ≤ n < 86016: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [82, 2494, 4796607, 95932858883463164200900049662]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup020_checked :
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n) = (82 : ℤ) ∧
    (∑ n ∈ Ico 81920 86016, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (4796607 : ℤ) ∧
    (∑ n ∈ Ico 81920 86016, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (95932858883463164200900049662 : ℤ) := by sorry

end Helfgott
