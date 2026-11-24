-- Prove2me | Theorems.Thm_GlobalTheory_clopen_image_irreducibleComponent
-- name    : GlobalTheory.clopen_image_irreducibleComponent
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:28.107341+00:00
-- url     : https://prove2.me/theorems/ec685b03-1eef-48e8-a1a5-e64123713460
-- title:
--   Global Theory: clopen image irreducible Component
-- statement:
--   The Global Theory construction uses the clopen image irreducible Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComponentSurjectsClopen.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComponentSurjectsClopen.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComponentSurjectsClopen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.clopen_image_irreducibleComponent : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by sorry
