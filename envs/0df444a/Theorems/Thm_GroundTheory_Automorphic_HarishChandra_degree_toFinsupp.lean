-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_degree_toFinsupp
-- name    : GroundTheory.Automorphic.HarishChandra.degree_toFinsupp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:46.207802+00:00
-- url     : https://prove2.me/theorems/f63d947b-f026-4a78-b7b1-bf5ef356dc45
-- title:
--   Harish Chandra: degree to Finsupp
-- statement:
--   The Harish Chandra construction uses the degree to Finsupp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L193-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L193-L196

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

theorem GroundTheory.Automorphic.HarishChandra.degree_toFinsupp (w : List (Fin n × Fin n)) :
    Finsupp.degree (Multiset.toFinsupp (w : Multiset (Fin n × Fin n))) = w.length := by sorry
