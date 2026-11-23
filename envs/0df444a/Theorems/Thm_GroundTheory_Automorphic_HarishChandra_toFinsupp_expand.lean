-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_toFinsupp_expand
-- name    : GroundTheory.Automorphic.HarishChandra.toFinsupp_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:57.81153+00:00
-- url     : https://prove2.me/theorems/0b0b56e0-74ca-4aca-a9b0-0915cd6e5e05
-- title:
--   Harish Chandra: to Finsupp expand
-- statement:
--   The Harish Chandra construction uses the to Finsupp expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L175-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L175-L178

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

theorem GroundTheory.Automorphic.HarishChandra.toFinsupp_expand (m : Fin n × Fin n →₀ ℕ) :
    Multiset.toFinsupp ((expand m : List _) : Multiset _) = m := by sorry
