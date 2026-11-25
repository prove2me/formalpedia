-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_component_surjects_clopen
-- name    : GlobalTheory.T.exists_component_surjects_clopen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:00.326557+00:00
-- url     : https://prove2.me/theorems/845b3288-4b21-4a5f-8452-3017e570dc51
-- title:
--   T: exists component surjects clopen
-- statement:
--   The T construction uses the exists component surjects clopen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComponentSurjectsClopenStatement.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComponentSurjectsClopenStatement.lean#L5-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComponentSurjectsClopen
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComponentSurjectsClopenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_component_surjects_clopen : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by sorry
