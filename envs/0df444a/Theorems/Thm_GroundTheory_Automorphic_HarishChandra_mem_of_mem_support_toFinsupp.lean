-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_of_mem_support_toFinsupp
-- name    : GroundTheory.Automorphic.HarishChandra.mem_of_mem_support_toFinsupp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:15.27449+00:00
-- url     : https://prove2.me/theorems/f3e68be3-3dcd-4d07-8bf3-43f0fc2ced62
-- title:
--   Harish Chandra: mem of mem support to Finsupp
-- statement:
--   The Harish Chandra construction uses the mem of mem support to Finsupp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L198-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L198-L201

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

theorem GroundTheory.Automorphic.HarishChandra.mem_of_mem_support_toFinsupp {w : List (Fin n × Fin n)} {a : Fin n × Fin n}
    (ha : a ∈ (Multiset.toFinsupp (w : Multiset _)).support) : a ∈ w := by sorry
