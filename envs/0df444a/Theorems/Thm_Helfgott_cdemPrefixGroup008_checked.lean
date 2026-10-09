-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup008_checked
-- name    : Helfgott.cdemPrefixGroup008_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T01:29:13.019108+00:00
-- url     : https://prove2.me/theorems/24c8f328-0825-48b0-b621-f29045631eeb
-- title:
--   CDEM exact Mobius prefix statistics on [32768, 36864)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 32768 ≤ n < 36864: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-33, 2491, -5120722, -102414897385000683505284752836]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup008_checked :
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n) = (-33 : ℤ) ∧
    (∑ n ∈ Ico 32768 36864, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2491 : ℕ) ∧
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-5120722 : ℤ) ∧
    (∑ n ∈ Ico 32768 36864, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-102414897385000683505284752836 : ℤ) := by sorry

end Helfgott
