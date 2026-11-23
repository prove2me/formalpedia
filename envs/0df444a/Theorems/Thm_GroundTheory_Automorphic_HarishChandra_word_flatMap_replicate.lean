-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_flatMap_replicate
-- name    : GroundTheory.Automorphic.HarishChandra.word_flatMap_replicate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:04.832528+00:00
-- url     : https://prove2.me/theorems/c1f163d8-a91c-4e5a-b17a-75ed0e00dda5
-- title:
--   Harish Chandra: word flat Map replicate
-- statement:
--   The Harish Chandra construction uses the word flat Map replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L146-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L146-L153

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

theorem GroundTheory.Automorphic.HarishChandra.word_flatMap_replicate (l : List (Fin n × Fin n)) (m : Fin n × Fin n → ℕ) :
    word (l.flatMap fun a => List.replicate (m a) a) = (l.map fun a => e a ^ m a).prod := by sorry
