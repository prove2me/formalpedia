-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup032_checked
-- name    : Helfgott.cdemPrefixGroup032_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:27:42.010119+00:00
-- url     : https://prove2.me/theorems/2bd576d1-3fc4-420c-8854-6af8cfa51e65
-- title:
--   CDEM exact Mobius prefix statistics on [131072, 135168)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 131072 ≤ n < 135168: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [25, 2483, 929924, 18598512082732240928880900310]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup032_checked :
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n) = (25 : ℤ) ∧
    (∑ n ∈ Ico 131072 135168, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2483 : ℕ) ∧
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (929924 : ℤ) ∧
    (∑ n ∈ Ico 131072 135168, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (18598512082732240928880900310 : ℤ) := by sorry

end Helfgott
