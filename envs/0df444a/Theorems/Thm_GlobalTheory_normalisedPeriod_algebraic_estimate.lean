-- Prove2me | Theorems.Thm_GlobalTheory_normalisedPeriod_algebraic_estimate
-- name    : GlobalTheory.normalisedPeriod_algebraic_estimate
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:01.439003+00:00
-- url     : https://prove2.me/theorems/5188a77d-955d-45d6-a0e5-0b8d0b196c0f
-- title:
--   Global Theory: normalised Period algebraic estimate
-- statement:
--   The Global Theory construction uses the normalised Period algebraic estimate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalisedPeriodAlgebraicEstimate.lean#L6-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalisedPeriodAlgebraicEstimate.lean#L6-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixMulEntryNormLeUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalisedPeriodAlgebraicEstimate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.normalisedPeriod_algebraic_estimate :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t →
      (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z →
      (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) →
      ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by sorry
