-- Prove2me | Theorems.Thm_GlobalTheory_DiffDecay_bounded_of_weak
-- name    : GlobalTheory.DiffDecay.bounded_of_weak
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:22.249448+00:00
-- url     : https://prove2.me/theorems/5c8b63c8-75cc-47ba-893d-6d7e211f397b
-- title:
--   Diff Decay: bounded of weak
-- statement:
--   The Diff Decay construction uses the bounded of weak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L24-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L24-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.DiffDecay
variable {E : Type} [AddCommGroup E] [Module ℂ E]

theorem GlobalTheory.DiffDecay.bounded_of_weak [TopologicalSpace E] [IsTopologicalAddGroup E] {T : Type} (f : T → E)
    (h : ∀ l : E →L[ℂ] ℂ, ∃ C : ℝ, ∀ t, ‖l (f t)‖ ≤ C) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ C : ℝ, ∀ t, p (f t) ≤ C := by sorry
