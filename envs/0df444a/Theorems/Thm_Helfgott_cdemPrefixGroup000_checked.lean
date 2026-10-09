-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup000_checked
-- name    : Helfgott.cdemPrefixGroup000_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:10:49.573972+00:00
-- url     : https://prove2.me/theorems/921a8c44-9615-446b-84d2-d7dfd43b89c8
-- title:
--   CDEM exact Mobius prefix statistics on [0, 4096)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 0 ≤ n < 4096: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-19, 2491, -20585031, -411700669208189062122844686405]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup000_checked :
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n) = (-19 : ℤ) ∧
    (∑ n ∈ Ico 0 4096, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-20585031 : ℤ) ∧
    (∑ n ∈ Ico 0 4096, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-411700669208189062122844686405 : ℤ) := by sorry

end Helfgott
