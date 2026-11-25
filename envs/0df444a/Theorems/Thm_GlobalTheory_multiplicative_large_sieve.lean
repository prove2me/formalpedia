-- Prove2me | Theorems.Thm_GlobalTheory_multiplicative_large_sieve
-- name    : GlobalTheory.multiplicative_large_sieve
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:56.82381+00:00
-- url     : https://prove2.me/theorems/20101a11-513a-4bb8-80c2-a7b8616e5b5d
-- title:
--   Global Theory: multiplicative large sieve
-- statement:
--   The Global Theory construction uses the multiplicative large sieve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultiplicativeLargeSieve.lean#L142-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultiplicativeLargeSieve.lean#L142-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussSumMulGaussSumInvOfIsPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultiplicativeLargeSieve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory

theorem GlobalTheory.multiplicative_large_sieve : ∀ (Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ Q → ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by sorry
