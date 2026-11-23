-- Prove2me | Theorems.Thm_GlobalTheory_additive_large_sieve
-- name    : GlobalTheory.additive_large_sieve
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:36.061796+00:00
-- url     : https://prove2.me/theorems/c382e85c-c85a-4c83-b36c-3d9f6a4e84a7
-- title:
--   Global Theory: additive large sieve
-- statement:
--   The Global Theory construction uses the additive large sieve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumIntervalIntegralLeOfSpaced.lean#L125-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumIntervalIntegralLeOfSpaced.lean#L125-L217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIntervalIntegralLeOfSpaced
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

theorem GlobalTheory.additive_large_sieve : ∀ (M N : ℕ) (a : ℕ → ℂ) (S : Finset ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ k : ℤ, δ ≤ |x - y - k|) → ∑ x ∈ S, ‖∑ n ∈ Finset.Ioc M (M + N), a n * Complex.exp (2 * Real.pi * I * n * x)‖ ^ 2 ≤ (1 / δ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by sorry
