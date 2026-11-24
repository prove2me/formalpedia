-- Prove2me | Theorems.Thm_GlobalTheory_sum_vonMangoldt_div_sq_tail
-- name    : GlobalTheory.sum_vonMangoldt_div_sq_tail
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:47.098842+00:00
-- url     : https://prove2.me/theorems/c31aac9b-fd03-4b35-9be4-d100f099a394
-- title:
--   Global Theory: sum von Mangoldt div sq tail
-- statement:
--   The Global Theory construction uses the sum von Mangoldt div sq tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumVonMangoldtDivSqTail.lean#L40-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumVonMangoldtDivSqTail.lean#L40-L52

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeomIccOneLeTwoMulSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
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

theorem GlobalTheory.sum_vonMangoldt_div_sq_tail
    (hψ : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ)) (M : ℕ) (hM : 1 ≤ M) (N : ℕ) :
    ∑ n ∈ Ioc M N, Λ n / (n : ℝ) ^ 2 ≤ 4 / M := by sorry
