-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_filt
-- name    : GroundTheory.Automorphic.HarishChandra.word_mem_filt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:31:07.040792+00:00
-- url     : https://prove2.me/theorems/ac01ac31-4a79-485c-a40f-fdb717b205f8
-- title:
--   Harish Chandra: word mem filt
-- statement:
--   The Harish Chandra construction uses the word mem filt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L298-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L298-L299

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

theorem GroundTheory.Automorphic.HarishChandra.word_mem_filt {w : List (Fin n × Fin n)} {d : ℕ} (h : w.length ≤ d) : word w ∈ filt (n := n) d := by sorry
