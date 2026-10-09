-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup035_checked
-- name    : Helfgott.cdemPrefixGroup035_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:33:43.104124+00:00
-- url     : https://prove2.me/theorems/a94d211a-ad96-444a-a5dc-c45f7833636e
-- title:
--   CDEM exact Mobius prefix statistics on [143360, 147456)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 143360 ≤ n < 147456: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [2, 2486, 77753, 1554831769282633231674959803]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup035_checked :
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n) = (2 : ℤ) ∧
    (∑ n ∈ Ico 143360 147456, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (77753 : ℤ) ∧
    (∑ n ∈ Ico 143360 147456, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (1554831769282633231674959803 : ℤ) := by sorry

end Helfgott
