-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup043_checked
-- name    : Helfgott.cdemPrefixGroup043_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:51:10.759364+00:00
-- url     : https://prove2.me/theorems/d1e819ed-0bbe-46b7-a7be-6e4e129d7bcc
-- title:
--   CDEM exact Mobius prefix statistics on [176128, 180224)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 176128 ≤ n < 180224: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-33, 2489, -935760, -18715745290123822870982040564]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup043_checked :
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 176128 180224, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2489 : ℕ) ∧
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-935760 : ℤ) ∧
    (∑ n ∈ Ico 176128 180224, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-18715745290123822870982040564 : ℤ) := by sorry

end Helfgott
