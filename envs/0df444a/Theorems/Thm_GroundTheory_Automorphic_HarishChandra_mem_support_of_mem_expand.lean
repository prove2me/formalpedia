-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_support_of_mem_expand
-- name    : GroundTheory.Automorphic.HarishChandra.mem_support_of_mem_expand
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:53:25.013115+00:00
-- url     : https://prove2.me/theorems/b70cedf7-af9f-48c0-bac7-54f287abf968
-- title:
--   Harish Chandra: mem support of mem expand
-- statement:
--   The Harish Chandra construction uses the mem support of mem expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L203-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L203-L206

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

theorem GroundTheory.Automorphic.HarishChandra.mem_support_of_mem_expand {m : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n}
    (ha : a ∈ expand m) : a ∈ m.support := by sorry
