-- Prove2me | Theorems.Thm_GlobalTheory_finite_and_ncard_le_of_forall_finset
-- name    : GlobalTheory.finite_and_ncard_le_of_forall_finset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:20.414909+00:00
-- url     : https://prove2.me/theorems/0c788e92-7733-4f8f-913f-8f1851165f5d
-- title:
--   Global Theory: finite and ncard le of forall finset
-- statement:
--   The Global Theory construction uses the finite and ncard le of forall finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L197-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L197-L210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric

theorem GlobalTheory.finite_and_ncard_le_of_forall_finset {α : Type*} (S : Set α) (B : ℝ)
    (h : ∀ s : Finset α, (s : Set α) ⊆ S → (s.card : ℝ) ≤ B) :
    S.Finite ∧ (S.ncard : ℝ) ≤ B := by sorry
