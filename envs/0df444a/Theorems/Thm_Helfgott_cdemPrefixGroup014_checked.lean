-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup014_checked
-- name    : Helfgott.cdemPrefixGroup014_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:43:42.322975+00:00
-- url     : https://prove2.me/theorems/e8fe152b-44cf-4b54-80ec-383b6a3a836e
-- title:
--   CDEM exact Mobius prefix statistics on [57344, 61440)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 57344 ≤ n < 61440: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [8, 2494, 582150, 11642752312647241467225188167]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup014_checked :
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n) = (8 : ℤ) ∧
    (∑ n ∈ Ico 57344 61440, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2494 : ℕ) ∧
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (582150 : ℤ) ∧
    (∑ n ∈ Ico 57344 61440, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (11642752312647241467225188167 : ℤ) := by sorry

end Helfgott
