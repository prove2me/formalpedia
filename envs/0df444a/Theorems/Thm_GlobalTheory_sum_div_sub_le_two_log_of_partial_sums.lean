-- Prove2me | Theorems.Thm_GlobalTheory_sum_div_sub_le_two_log_of_partial_sums
-- name    : GlobalTheory.sum_div_sub_le_two_log_of_partial_sums
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:04.52488+00:00
-- url     : https://prove2.me/theorems/ef1c7327-1821-4c5a-b83a-8f8a6013ab6d
-- title:
--   Global Theory: sum div sub le two log of partial sums
-- statement:
--   The Global Theory construction uses the sum div sub le two log of partial sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumDivSubLeTwoLogOfPartialSums.lean#L8-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumDivSubLeTwoLogOfPartialSums.lean#L8-L40

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory

theorem GlobalTheory.sum_div_sub_le_two_log_of_partial_sums (a : ℕ → ℝ)
    (h : ∀ N : ℕ, ∑ n ∈ Icc 1 N, a n ≤ 2 * (N : ℝ)) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n / (n : ℝ) - (∑ n ∈ Icc 1 N, a n) / ((N : ℝ) + 1)
      ≤ 2 * Real.log ((N : ℝ) + 1) := by sorry
