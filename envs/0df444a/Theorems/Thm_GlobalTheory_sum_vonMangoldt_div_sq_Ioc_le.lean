-- Prove2me | Theorems.Thm_GlobalTheory_sum_vonMangoldt_div_sq_Ioc_le
-- name    : GlobalTheory.sum_vonMangoldt_div_sq_Ioc_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:36.875574+00:00
-- url     : https://prove2.me/theorems/4c7d7893-4a2b-4460-90c4-fa248d9a1ee4
-- title:
--   Global Theory: sum von Mangoldt div sq Ioc le
-- statement:
--   The Global Theory construction uses the sum von Mangoldt div sq Ioc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumVonMangoldtDivSqIocLe.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumVonMangoldtDivSqIocLe.lean#L39-L51

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

theorem GlobalTheory.sum_vonMangoldt_div_sq_Ioc_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤ 4 / (K : ℝ) := by sorry
