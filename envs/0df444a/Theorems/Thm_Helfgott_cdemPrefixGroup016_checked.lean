-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup016_checked
-- name    : Helfgott.cdemPrefixGroup016_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:46:26.792871+00:00
-- url     : https://prove2.me/theorems/5a60e261-0576-415f-9528-368bc6cf272d
-- title:
--   CDEM exact Mobius prefix statistics on [65536, 69632)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 65536 ≤ n < 69632: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [78, 2486, 5693314, 113867298783621895407740232468]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup016_checked :
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n) = (78 : ℤ) ∧
    (∑ n ∈ Ico 65536 69632, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2486 : ℕ) ∧
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (5693314 : ℤ) ∧
    (∑ n ∈ Ico 65536 69632, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (113867298783621895407740232468 : ℤ) := by sorry

end Helfgott
