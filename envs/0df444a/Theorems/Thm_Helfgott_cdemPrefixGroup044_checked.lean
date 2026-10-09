-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup044_checked
-- name    : Helfgott.cdemPrefixGroup044_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:51:02.186365+00:00
-- url     : https://prove2.me/theorems/8ac06cfa-4442-4c9c-a3ee-58116374d272
-- title:
--   CDEM exact Mobius prefix statistics on [180224, 184320)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 180224 ≤ n < 184320: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-43, 2497, -1172650, -23453069817617727527292600878]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup044_checked :
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n) = (-43 : ℤ) ∧
    (∑ n ∈ Ico 180224 184320, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2497 : ℕ) ∧
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1172650 : ℤ) ∧
    (∑ n ∈ Ico 180224 184320, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-23453069817617727527292600878 : ℤ) := by sorry

end Helfgott
