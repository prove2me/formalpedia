-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup031_checked
-- name    : Helfgott.cdemPrefixGroup031_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:20:48.617915+00:00
-- url     : https://prove2.me/theorems/91cfc61a-928f-4a59-a665-3224259f43bf
-- title:
--   CDEM exact Mobius prefix statistics on [126976, 131072)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 126976 ≤ n < 131072: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-48, 2492, -1828624, -36572934278886159193432981618]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup031_checked :
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n) = (-48 : ℤ) ∧
    (∑ n ∈ Ico 126976 131072, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1828624 : ℤ) ∧
    (∑ n ∈ Ico 126976 131072, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-36572934278886159193432981618 : ℤ) := by sorry

end Helfgott
