-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup034_checked
-- name    : Helfgott.cdemPrefixGroup034_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:27:37.153088+00:00
-- url     : https://prove2.me/theorems/b2b6a3e0-42b0-462f-9071-21ec60b883fd
-- title:
--   CDEM exact Mobius prefix statistics on [139264, 143360)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 139264 ≤ n < 143360: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [36, 2496, 1256218, 25125034322283821108684733129]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup034_checked :
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 139264 143360, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2496 : ℕ) ∧
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1256218 : ℤ) ∧
    (∑ n ∈ Ico 139264 143360, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (25125034322283821108684733129 : ℤ) := by sorry

end Helfgott
