-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_isClopen_mem_disjoint
-- name    : GroundTheory.Automorphic.Whittaker.exists_isClopen_mem_disjoint
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:05.202768+00:00
-- url     : https://prove2.me/theorems/42f080a7-9eff-48ff-9119-c72d736c9f90
-- title:
--   Whittaker: exists is Clopen mem disjoint
-- statement:
--   The Whittaker construction uses the exists is Clopen mem disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L172-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L172-L176

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem GroundTheory.Automorphic.Whittaker.exists_isClopen_mem_disjoint {Q : Set X} (hQ : IsCompact Q) {y : X} (hy : y ∉ Q) :
    ∃ V : Set X, IsClopen V ∧ y ∈ V ∧ Disjoint V Q := by sorry
