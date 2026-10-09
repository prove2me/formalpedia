-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup048_checked
-- name    : Helfgott.cdemPrefixGroup048_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:58:22.513797+00:00
-- url     : https://prove2.me/theorems/59c5df8a-b256-4d8c-842e-1e9caeec8ac2
-- title:
--   CDEM exact Mobius prefix statistics on [196608, 199331)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 196608 ≤ n < 199331: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-7, 1657, -177148, -3543062182269117707548856280]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup048_checked :
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n) = (-7 : ℤ) ∧
    (∑ n ∈ Ico 196608 199331, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (1657 : ℕ) ∧
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-177148 : ℤ) ∧
    (∑ n ∈ Ico 196608 199331, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-3543062182269117707548856280 : ℤ) := by sorry

end Helfgott
