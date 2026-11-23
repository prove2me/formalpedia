-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_canonSpan
-- name    : GroundTheory.Automorphic.HarishChandra.word_mem_canonSpan
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:56.438321+00:00
-- url     : https://prove2.me/theorems/70d81b6a-0fd9-4952-8e37-e0dab66242ea
-- title:
--   Harish Chandra: word mem canon Span
-- statement:
--   The Harish Chandra construction uses the word mem canon Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L227-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L227-L260

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.word_mem_canonSpan {P : Fin n × Fin n → Prop} (hP : Closed P) :
    ∀ (w : List (Fin n × Fin n)), (∀ a ∈ w, P a) →
      word w ∈ canonSpan P (min 1 w.length) w.length := by sorry
