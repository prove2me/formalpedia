-- Prove2me | Theorems.Thm_GlobalTheory_MultSieve_sum_primitive_le
-- name    : GlobalTheory.MultSieve.sum_primitive_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:46.802339+00:00
-- url     : https://prove2.me/theorems/1119f62f-e940-40bc-9f06-c0147546f9d8
-- title:
--   Mult Sieve: sum primitive le
-- statement:
--   The Mult Sieve construction uses the sum primitive le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultiplicativeLargeSieve.lean#L47-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultiplicativeLargeSieve.lean#L47-L96

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
open GlobalTheory GlobalTheory.MultSieve

theorem GlobalTheory.MultSieve.sum_primitive_le {q : ℕ} [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ q | χ.IsPrimitive}, ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by sorry
