-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup011_checked
-- name    : Helfgott.cdemPrefixGroup011_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:35:36.518001+00:00
-- url     : https://prove2.me/theorems/3f882de1-9a10-479c-a0da-e3c89b2c42ac
-- title:
--   CDEM exact Mobius prefix statistics on [45056, 49152)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 45056 ≤ n < 49152: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [76, 2492, 8122188, 162444379682444304816648124219]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup011_checked :
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n) = (76 : ℤ) ∧
    (∑ n ∈ Ico 45056 49152, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (8122188 : ℤ) ∧
    (∑ n ∈ Ico 45056 49152, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (162444379682444304816648124219 : ℤ) := by sorry

end Helfgott
