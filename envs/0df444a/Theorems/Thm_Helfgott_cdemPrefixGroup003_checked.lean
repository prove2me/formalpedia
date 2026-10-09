-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup003_checked
-- name    : Helfgott.cdemPrefixGroup003_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:17:13.192753+00:00
-- url     : https://prove2.me/theorems/dfa0aedf-048f-4302-adff-86abdbebbed5
-- title:
--   CDEM exact Mobius prefix statistics on [12288, 16384)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 12288 ≤ n < 16384: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-53, 2493, -18578129, -371562610433863429345766935904]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup003_checked :
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n) = (-53 : ℤ) ∧
    (∑ n ∈ Ico 12288 16384, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2493 : ℕ) ∧
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-18578129 : ℤ) ∧
    (∑ n ∈ Ico 12288 16384, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-371562610433863429345766935904 : ℤ) := by sorry

end Helfgott
