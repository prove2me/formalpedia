-- Prove2me | Theorems.Thm_GlobalTheory_SublatticeFacts_main
-- name    : GlobalTheory.SublatticeFacts.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:24.4288+00:00
-- url     : https://prove2.me/theorems/62cc4fa8-da01-49bf-afef-e028190b6556
-- title:
--   Sublattice Facts: main
-- statement:
--   The Sublattice Facts construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsBisExtra.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsBisExtra.lean#L33-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisExtra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SublatticeFacts
open Matrix

theorem GlobalTheory.SublatticeFacts.main : ∀ {A : Type} [inst : CommRing A] {S : Subring A} {n : Type} [inst_1 : Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)), Submodule.FG Λ →
    (∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) →
    ∀ (X : Matrix n n A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ := by sorry
