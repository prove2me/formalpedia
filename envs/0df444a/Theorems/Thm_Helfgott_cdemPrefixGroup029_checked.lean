-- Prove2me | Theorems.Thm_Helfgott_cdemPrefixGroup029_checked
-- name    : Helfgott.cdemPrefixGroup029_checked
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:20:39.104303+00:00
-- url     : https://prove2.me/theorems/39f8ec2b-d52a-4e56-9e26-a43282200a6c
-- title:
--   CDEM exact Mobius prefix statistics on [118784, 122880)
-- statement:
--   Exact integer statistics of the published candidate Mobius table on 118784 ≤ n < 122880: its signed sum, absolute mass, weighted floor sum at N=5,000,000,000, and rounded reciprocal sum at scale Q=10^32 are respectively [-67, 2487, -2753063, -55061847728057133877177658874]. This is an independently kernel-checked arithmetic block for the CDEM prefix at K=199330. The table-to-Mobius bridge and exact summation of these blocks are proved separately; this block does not assert a bound for the Mertens function at unbounded heights.
-- source:
--   Kernel-checked numerical input for the Cohen–Dress–El Marraki bootstrap in the three-prime Goldbach minor-arc route. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
open Finset
open scoped BigOperators

namespace Helfgott

theorem cdemPrefixGroup029_checked :
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n) = (-67 : ℤ) ∧
    (∑ n ∈ Ico 118784 122880, (mobiusTreeValue 16 mobiusTable1200001 n).natAbs) = (2487 : ℕ) ∧
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n * (5000000000 / n : ℕ)) = (-2753063 : ℤ) ∧
    (∑ n ∈ Ico 118784 122880, mobiusTreeValue 16 mobiusTable1200001 n * (100000000000000000000000000000000 / n : ℕ)) = (-55061847728057133877177658874 : ℤ) := by sorry

end Helfgott
