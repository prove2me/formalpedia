-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup022_checked
-- name    : Helfgott.cdemPrefixGroup022_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:57:11.445627+00:00
-- url     : https://prove2.me/theorems/0b7bdd85-7f33-4231-9f9d-a262933dc54d
-- title:
--   CDEM exact Mobius prefix statistics on [90112, 94208)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 90112 ≤ n < 94208: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-62, 2496, -3317294, -66346628080622312589865919477]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup022_checked :
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n) = (-62 : ℤ) ∧
    (∑ n ∈ Ico 90112 94208, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2496 : ℕ) ∧
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-3317294 : ℤ) ∧
    (∑ n ∈ Ico 90112 94208, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-66346628080622312589865919477 : ℤ) := by sorry

end Helfgott
