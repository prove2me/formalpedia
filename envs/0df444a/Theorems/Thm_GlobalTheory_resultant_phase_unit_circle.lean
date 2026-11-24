-- Prove2me | Theorems.Thm_GlobalTheory_resultant_phase_unit_circle
-- name    : GlobalTheory.resultant_phase_unit_circle
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:18.927305+00:00
-- url     : https://prove2.me/theorems/7882a87e-2093-46b1-8717-834a2c1dd75e
-- title:
--   Global Theory: resultant phase unit circle
-- statement:
--   The Global Theory construction uses the resultant phase unit circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjSubMulNegMulOfNormOne.lean#L19-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjSubMulNegMulOfNormOne.lean#L19-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjSubMulNegMulOfNormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.resultant_phase_unit_circle :
    ∀ (a b : ℕ) (α : Fin a → ℂ) (β : Fin b → ℂ), (∀ i, ‖α i‖ = 1) → (∀ j, ‖β j‖ = 1) →
      (∀ i j, α i ≠ β j) → ∀ k : ℤ, let R : ℂ := ∏ i, ∏ j, (α i - β j);
      (R / (‖R‖ : ℂ)) ^ (2 * k - 1) * (‖R‖ : ℂ) =
        (starRingEnd ℂ) R * ((-1 : ℂ) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ k := by sorry
