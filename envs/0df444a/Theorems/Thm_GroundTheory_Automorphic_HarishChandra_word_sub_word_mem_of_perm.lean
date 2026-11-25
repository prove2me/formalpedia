-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_sub_word_mem_of_perm
-- name    : GroundTheory.Automorphic.HarishChandra.word_sub_word_mem_of_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:00.997471+00:00
-- url     : https://prove2.me/theorems/75788fc2-4893-45b7-8848-e206f982fe80
-- title:
--   Harish Chandra: word sub word mem of perm
-- statement:
--   The Harish Chandra construction uses the word sub word mem of perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L83-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L83-L106

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

theorem GroundTheory.Automorphic.HarishChandra.word_sub_word_mem_of_perm {P : Fin n × Fin n → Prop} (hP : Closed P)
    {w w' : List (Fin n × Fin n)} (h : w.Perm w') (hw : ∀ a ∈ w, P a) :
    word w - word w' ∈ wordSpan P (w.length - 1) := by sorry
