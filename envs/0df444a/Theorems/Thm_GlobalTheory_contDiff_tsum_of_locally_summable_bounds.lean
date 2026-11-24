-- Prove2me | Theorems.Thm_GlobalTheory_contDiff_tsum_of_locally_summable_bounds
-- name    : GlobalTheory.contDiff_tsum_of_locally_summable_bounds
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:46.713772+00:00
-- url     : https://prove2.me/theorems/3fa50ba8-e628-40f1-a601-19d2f61a1f8e
-- title:
--   Global Theory: cont Diff tsum of locally summable bounds
-- statement:
--   The Global Theory construction uses the cont Diff tsum of locally summable bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffTsumOfLocallySummableBounds.lean#L7-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffTsumOfLocallySummableBounds.lean#L7-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffTsumOfLocallySummableBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.contDiff_tsum_of_locally_summable_bounds {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i))
    (hu : ∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧
      ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by sorry
