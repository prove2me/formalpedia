-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_perm_expand
-- name    : GroundTheory.Automorphic.HarishChandra.perm_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:59.011891+00:00
-- url     : https://prove2.me/theorems/6fcfd763-221d-48ab-8a65-48caca27a014
-- title:
--   Harish Chandra: perm expand
-- statement:
--   The Harish Chandra construction uses the perm expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L180-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L180-L184

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

theorem GroundTheory.Automorphic.HarishChandra.perm_expand (w : List (Fin n × Fin n)) :
    w.Perm (expand (Multiset.toFinsupp (w : Multiset _))) := by sorry
