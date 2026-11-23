-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_wordSpan
-- name    : GroundTheory.Automorphic.HarishChandra.word_mem_wordSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:52.427904+00:00
-- url     : https://prove2.me/theorems/cb954144-2e0b-4e69-a80a-1e4d27c1d9e3
-- title:
--   Harish Chandra: word mem word Span
-- statement:
--   The Harish Chandra construction uses the word mem word Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L32-L34

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

theorem GroundTheory.Automorphic.HarishChandra.word_mem_wordSpan {P : Fin n × Fin n → Prop} {w : List (Fin n × Fin n)}
    (hw : ∀ a ∈ w, P a) : word w ∈ wordSpan P w.length := by sorry
