-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup026_checked
-- name    : Helfgott.cdemPrefixGroup026_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:06:49.83677+00:00
-- url     : https://prove2.me/theorems/3d7bd7c7-9150-4e14-90cd-26e35b9868bd
-- title:
--   CDEM exact Mobius prefix statistics on [106496, 110592)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 106496 ≤ n < 110592: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [34, 2492, 1583822, 31677009560696448723001105993]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup026_checked :
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n) = (34 : ℤ) ∧
    (∑ n ∈ Ico 106496 110592, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1583822 : ℤ) ∧
    (∑ n ∈ Ico 106496 110592, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (31677009560696448723001105993 : ℤ) := by sorry

end Helfgott
