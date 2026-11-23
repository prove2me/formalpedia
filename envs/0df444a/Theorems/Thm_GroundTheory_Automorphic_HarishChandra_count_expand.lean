-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_count_expand
-- name    : GroundTheory.Automorphic.HarishChandra.count_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:51.261149+00:00
-- url     : https://prove2.me/theorems/47f5c31a-08f2-4472-bf76-a85adb248567
-- title:
--   Harish Chandra: count expand
-- statement:
--   The Harish Chandra construction uses the count expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L159-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L159-L173

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

theorem GroundTheory.Automorphic.HarishChandra.count_expand (m : Fin n × Fin n →₀ ℕ) (a : Fin n × Fin n) :
    Multiset.count a ((expand m : List _) : Multiset _) = m a := by sorry
