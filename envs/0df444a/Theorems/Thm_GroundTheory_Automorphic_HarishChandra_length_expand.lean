-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_length_expand
-- name    : GroundTheory.Automorphic.HarishChandra.length_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:41.286053+00:00
-- url     : https://prove2.me/theorems/2a897ac5-e46f-4a8e-86d5-c42ab7033df1
-- title:
--   Harish Chandra: length expand
-- statement:
--   The Harish Chandra construction uses the length expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L186-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/MemOfMemSupportToFinsupp.lean#L186-L191

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

theorem GroundTheory.Automorphic.HarishChandra.length_expand (m : Fin n × Fin n →₀ ℕ) : (expand m).length = m.degree := by sorry
