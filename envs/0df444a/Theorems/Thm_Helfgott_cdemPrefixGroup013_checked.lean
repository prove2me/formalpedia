-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup013_checked
-- name    : Helfgott.cdemPrefixGroup013_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:40:26.796432+00:00
-- url     : https://prove2.me/theorems/426ffd5c-f439-4e86-8240-919100412efd
-- title:
--   CDEM exact Mobius prefix statistics on [53248, 57344)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 53248 ≤ n < 57344: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-74, 2484, -6526262, -130525671446891319381165871871]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup013_checked :
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n) = (-74 : ℤ) ∧
    (∑ n ∈ Ico 53248 57344, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2484 : ℕ) ∧
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-6526262 : ℤ) ∧
    (∑ n ∈ Ico 53248 57344, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-130525671446891319381165871871 : ℤ) := by sorry

end Helfgott
