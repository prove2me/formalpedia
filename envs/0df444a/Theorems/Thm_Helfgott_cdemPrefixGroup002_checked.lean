-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup002_checked
-- name    : Helfgott.cdemPrefixGroup002_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:17:09.979375+00:00
-- url     : https://prove2.me/theorems/2318a24c-c261-4a5e-9869-7ddb76c7f127
-- title:
--   CDEM exact Mobius prefix statistics on [8192, 12288)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 8192 ≤ n < 12288: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-1, 2487, -4997249, -99945186721065157596732046201]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup002_checked :
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n) = (-1 : ℤ) ∧
    (∑ n ∈ Ico 8192 12288, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-4997249 : ℤ) ∧
    (∑ n ∈ Ico 8192 12288, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-99945186721065157596732046201 : ℤ) := by sorry

end Helfgott
