-- Prove2me | Theorems.Thm_GlobalTheory_sum_von_mangoldt_div_sq_Ioc_le
-- name    : GlobalTheory.sum_von_mangoldt_div_sq_Ioc_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:45.385786+00:00
-- url     : https://prove2.me/theorems/d8f9655d-d6de-45e3-bbfc-b795d020cb4f
-- title:
--   Global Theory: sum von mangoldt div sq Ioc le
-- statement:
--   The Global Theory construction uses the sum von mangoldt div sq Ioc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumVonMangoldtDivSqIocLe.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumVonMangoldtDivSqIocLe.lean#L9-L37

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
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

theorem GlobalTheory.sum_von_mangoldt_div_sq_Ioc_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) (hM : K ≤ M) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤
      (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 + 4 / (K : ℝ) - 4 / (M : ℝ) := by sorry
