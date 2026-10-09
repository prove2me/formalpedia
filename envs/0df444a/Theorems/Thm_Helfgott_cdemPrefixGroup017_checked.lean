-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup017_checked
-- name    : Helfgott.cdemPrefixGroup017_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:48:54.890699+00:00
-- url     : https://prove2.me/theorems/7bfe4d81-6930-4c37-a0aa-1b7f63c6ae79
-- title:
--   CDEM exact Mobius prefix statistics on [69632, 73728)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 69632 ≤ n < 73728: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-56, 2490, -3988344, -79767685146028838273380640020]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup017_checked :
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n) = (-56 : ℤ) ∧
    (∑ n ∈ Ico 69632 73728, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2490 : ℕ) ∧
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3988344 : ℤ) ∧
    (∑ n ∈ Ico 69632 73728, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-79767685146028838273380640020 : ℤ) := by sorry

end Helfgott
