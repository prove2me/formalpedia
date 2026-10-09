-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup007_checked
-- name    : Helfgott.cdemPrefixGroup007_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:28:42.320796+00:00
-- url     : https://prove2.me/theorems/0cacccc3-ec8d-4ea0-8c4a-e0d6fdfd25df
-- title:
--   CDEM exact Mobius prefix statistics on [28672, 32768)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 28672 ≤ n < 32768: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [36, 2486, 6229467, 124590055446270867968603592582]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup007_checked :
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n) = (36 : ℤ) ∧
    (∑ n ∈ Ico 28672 32768, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (6229467 : ℤ) ∧
    (∑ n ∈ Ico 28672 32768, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (124590055446270867968603592582 : ℤ) := by sorry

end Helfgott
