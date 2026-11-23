-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
-- name    : GroundTheory.Automorphic.HarishChandra.expand_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:28.399278+00:00
-- url     : https://prove2.me/theorems/908623a8-3ef4-461e-97d1-a327e490485a
-- title:
--   Harish Chandra: expand zero
-- statement:
--   The Harish Chandra construction uses the expand zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L207-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L207-L208

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

theorem GroundTheory.Automorphic.HarishChandra.expand_zero : expand (0 : Fin n × Fin n →₀ ℕ) = [] := by sorry
