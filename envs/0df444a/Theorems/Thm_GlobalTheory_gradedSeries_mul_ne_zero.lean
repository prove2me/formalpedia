-- Prove2me | Theorems.Thm_GlobalTheory_gradedSeries_mul_ne_zero
-- name    : GlobalTheory.gradedSeries_mul_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:42.172076+00:00
-- url     : https://prove2.me/theorems/04f17108-b685-4b0b-a3ad-a6dadbf9f2ec
-- title:
--   Global Theory: graded Series mul ne zero
-- statement:
--   The Global Theory construction uses the graded Series mul ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/GradedSeriesMulNeZero.lean#L7-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/GradedSeriesMulNeZero.lean#L7-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_GradedSeriesMulNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Metric Set
open GlobalTheory

theorem GlobalTheory.gradedSeries_mul_ne_zero : ∀ (ι : Type) (deg : ι → ℕ) (a : ι → ℂ) (ρ δ : ℝ) (P Q : ℂ → ℂ), 0 < δ → Differentiable ℂ P → Differentiable ℂ Q → (∀ r : ℝ, 0 < r → r < ρ → Summable fun i => ‖a i‖ * r ^ deg i) → (∀ x : ℝ, 0 < x → x < δ → (∑' i, a i * (x : ℂ) ^ deg i) * P x = Q x) → ∀ X : ℂ, ‖X‖ < ρ → Q X ≠ 0 → P X ≠ 0 := by sorry
