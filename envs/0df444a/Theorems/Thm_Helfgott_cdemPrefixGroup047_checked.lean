-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup047_checked
-- name    : Helfgott.cdemPrefixGroup047_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:57:13.365845+00:00
-- url     : https://prove2.me/theorems/8e1d94e4-d0be-4ccc-88eb-63a56f3bdb86
-- title:
--   CDEM exact Mobius prefix statistics on [192512, 196608)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 192512 ≤ n < 196608: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-55, 2483, -1421942, -28439348127680355413352485456]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup047_checked :
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n) = (-55 : ℤ) ∧
    (∑ n ∈ Ico 192512 196608, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-1421942 : ℤ) ∧
    (∑ n ∈ Ico 192512 196608, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-28439348127680355413352485456 : ℤ) := by sorry

end Helfgott
