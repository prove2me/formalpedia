-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_singleton
-- name    : GroundTheory.Automorphic.HarishChandra.word_singleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:04.988102+00:00
-- url     : https://prove2.me/theorems/41793d95-6b0e-464c-a870-f2d12e1a0b08
-- title:
--   Harish Chandra: word singleton
-- statement:
--   The Harish Chandra construction uses the word singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemCenterOfCommuteE.lean#L28-L28

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

theorem GroundTheory.Automorphic.HarishChandra.word_singleton (a : Fin n × Fin n) : word [a] = e a := by sorry
