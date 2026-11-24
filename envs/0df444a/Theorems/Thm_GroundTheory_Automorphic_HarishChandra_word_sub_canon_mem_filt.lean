-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_sub_canon_mem_filt
-- name    : GroundTheory.Automorphic.HarishChandra.word_sub_canon_mem_filt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:59.763421+00:00
-- url     : https://prove2.me/theorems/4e1cbfef-f9d3-42be-bc69-2da6dff05a64
-- title:
--   Harish Chandra: word sub canon mem filt
-- statement:
--   The Harish Chandra construction uses the word sub canon mem filt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L315-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L315-L317

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

theorem GroundTheory.Automorphic.HarishChandra.word_sub_canon_mem_filt (w : List (Fin n × Fin n)) :
    word w - canon (Multiset.toFinsupp (w : Multiset _)) ∈ filt (n := n) (w.length - 1) := by sorry
