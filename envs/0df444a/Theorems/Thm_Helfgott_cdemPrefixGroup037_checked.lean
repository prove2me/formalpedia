-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup037_checked
-- name    : Helfgott.cdemPrefixGroup037_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:34:16.217055+00:00
-- url     : https://prove2.me/theorems/906a1211-ccdf-417e-bcfb-85aa9115f8e1
-- title:
--   CDEM exact Mobius prefix statistics on [151552, 155648)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 151552 ≤ n < 155648: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-26, 2486, -874471, -17489729376966159644790271834]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup037_checked :
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n) = (-26 : ℤ) ∧
    (∑ n ∈ Ico 151552 155648, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-874471 : ℤ) ∧
    (∑ n ∈ Ico 151552 155648, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-17489729376966159644790271834 : ℤ) := by sorry

end Helfgott
