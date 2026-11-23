-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_letters
-- name    : GroundTheory.Automorphic.HarishChandra.mem_letters
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:04.048639+00:00
-- url     : https://prove2.me/theorems/52d449c8-6f5f-4c7f-8e6e-8e801233ce7e
-- title:
--   Harish Chandra: mem letters
-- statement:
--   The Harish Chandra construction uses the mem letters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L113-L120

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

theorem GroundTheory.Automorphic.HarishChandra.mem_letters (a : Fin n × Fin n) : a ∈ letters n := by sorry
