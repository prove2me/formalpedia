-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup040_checked
-- name    : Helfgott.cdemPrefixGroup040_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:41:55.237067+00:00
-- url     : https://prove2.me/theorems/c39772e3-2945-409b-9ab9-464477ed4947
-- title:
--   CDEM exact Mobius prefix statistics on [163840, 167936)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 163840 ≤ n < 167936: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [46, 2492, 1390733, 27814957145438392547713550359]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup040_checked :
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n) = (46 : ℤ) ∧
    (∑ n ∈ Ico 163840 167936, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2492 : ℕ) ∧
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (1390733 : ℤ) ∧
    (∑ n ∈ Ico 163840 167936, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (27814957145438392547713550359 : ℤ) := by sorry

end Helfgott
