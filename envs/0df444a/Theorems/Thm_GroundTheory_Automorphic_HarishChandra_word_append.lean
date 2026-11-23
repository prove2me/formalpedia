-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
-- name    : GroundTheory.Automorphic.HarishChandra.word_append
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:41.883424+00:00
-- url     : https://prove2.me/theorems/5596a8be-e81e-4f36-bdf6-0ecb7067e9c8
-- title:
--   Harish Chandra: word append
-- statement:
--   The Harish Chandra construction uses the word append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L25-L26

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
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

theorem GroundTheory.Automorphic.HarishChandra.word_append (v w : List (Fin n × Fin n)) : word (v ++ w) = word v * word w := by sorry
